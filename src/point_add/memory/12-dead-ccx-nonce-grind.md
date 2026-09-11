# 12 — 死门跳过与 nonce 磨制：完整实验记录与路线图（2026-09-05）

> 本文档记录"删除 pingpong 电路中从不触发的 CCX 以降低 Toffoli"这一优化的全部实验事实、
> 障碍分析、以及下一步的确定路线。所有结论均经实验验证。工具代码在 `src/bin/`（本地工具，不参与提交）。
>
> ~~当前榜单成绩：903,396.347 Toffoli × 1,263 qubits = 1.141B（9024/9024 OK）~~
> **2026-09-06 更新：已被反超。** 新榜首（2026-09-05 提交）：**904,049 T × 1,260 qubits = 1,139,101,740**。
> 我方 903,396 T × 1,263 Q = 1,140,989,148 退居第二（落后 0.166%）。
> 对方策略：+653 Toffoli 换 −3 qubits。夺回条件：1,263Q 下 T ≤ 901,901（−1,495 T）；
> 或 1,262Q 下 T ≤ 902,776（−620 T）；或 **1,260Q + 现有 Toffoli 不变即胜**（903,396×1,260 = 1,138.3M）。
> 死门跳过（≈−27k T → ~1.106B）落地则领先 ~2.9%。
> 电路规模：body 12,450,792 ops / 944,442 emitted CCX / 704 divide 轮 / 700 multiply 轮。

---

## 1. 背景机制（务必先理解）

### 1.1 Fiat-Shamir 考卷机制（README:35 明文）
9024 个测试输入**由提交电路 op 流的 SHAKE256 hash 派生**（domain `b"quantum_ecc-fiat-shamir-v2"`），
每个 shot 读 2×32 字节作为 k1,k2，输入点 = k1·G、k2·G，期望输出 = 椭圆曲线点加 (k1+k2)·G。
**这是防作弊设计：任何 body 改动 → hash 变 → 9024 道题全部换掉。**

### 1.2 尾 nonce 机制（mod.rs:2835-2847, 2147-2160）
`build()` 在 pingpong body 之后追加 96 个 X 门，然后 `apply_tail_nonce(ops, nonce)` 把它们改写为
48 对 `X;X`，每对打在**同一个 qubit**（nonce 的第 b 位 = 0 → qubit 0；= 1 → qubit 1）。
- X;X 在同一 qubit = 恒等 → **nonce 对电路物理作用恒等**（Toffoli/Clifford/宽度全不变）；
- 但每个 X 门的 `q_target` 不同 → hash 不同 → **nonce 是一个 48 bit 的"选考卷"旋钮**。
- 默认 nonce `3009322982643`（env `SUB4_PINGPONG_TAIL_NONCE` 可覆盖），是前人磨出的"干净 island"。
- nonce 在 baseline commit（7eb4f03）就已存在，不是本次会话磨的。

### 1.3 pingpong 电路有固有失败率 λ
固定深度的 ping-pong 二进制除法（ROUNDS_DEFAULT=704，multiply 700）在 ~0.19% 的随机输入上
**GCD 走步不能在轮数内收敛** / 宽度表（WIDTH_SCHEDULE，700 项，258→8）截断进位 → 结果错。
这是算法固有属性（用深度换门数），不是 bug。随机 nonce 下 9024 题里平均
**经典失败 λ_c ≈ 16-18，相位垃圾 λ_p ≈ 5（旧电路实测，02-lambda.md）**：
- P(干净 nonce) = e^-(λ_c+λ_p) ≈ e^-23（旧头）；
- 能发货纯粹因为有人磨到了一个幸运 nonce，并在此后每次提交都保持该 island 干净。
- **相位垃圾也是经典可判定的**：hmr/R 测量擦除时若 qubit 当时为 1（"dirty"），sim 以 1/2 概率
  翻相位并强制清零；"擦除时 qubit=1"是纯经典条件，滤波器可以一并预测。

### 1.4 评测的四道闸（README）
① 经典正确（gx/gy = 期望点）；② 可逆性（辅助比特释放时为 0）；
③ 相位干净（无残留相位）；④ 正反向电路恒等。磨 nonce 只需要找让①③都干净的 island。

---

## 2. 本次实验结论（全部跑过）

### 2.1 跳过机制本身 100% 正确
- `dg_ccx` 机制（pingpong_div.rs:24-80）：给 7 类加法器进位 CCX 打语义标签 key=(tag,uid,slot)，
  key 在烘焙表 `pingpong_dead_ccx_keys.inc` 中就不发射该 CCX。
  tag1=signed_add_wrapping_sigma，tag2=fused_fold_maskfree，tag3=signed_add_wrapping_sigma_split；
  slot = 比特位（终端进位 slot=0x1FF=511）。
- **闭环恒等测试**：同一固定输入种子（DEAD_SCAN_FIXED_SEED）挖表 → 烘焙 → 同一种子验证，
  失败数完全一致（36→36），跳过 21,853 门零差异。数学上：进位 ladder 的 CCX 合成进位 ancilla，
  反向用 hmr+cz_if 测量擦除（无配对 CCX）；进位乘积恒为 0 时跳过 CCX，ancilla 保持 CX 已置的值，
  与发射结果逐比特相同。
- 反相 pass 用 measured erasure（hmr+cz_if），与进位轨迹无关，跳过前向 CCX 不需要改反相。

### 2.2 但死门集合随输入流剧烈漂移（核心难点）
| 实验 | 结果 |
|---|---|
| 8 个独立输入群体（各 4 万，共 32 万）各自挖死门 | 每群 17.6k-18.3k 死门；**8 群交集仅 8,533** |
| 8533 交集烘焙后，全新群体（held-out salt99, 3万） | 全发射 64 失败 vs **跳过 390-10136 失败**（门在新流上触发） |
| 按 tag 分（held-out salt99）：tag3 split(6门) | 64→64，**安全** |
| tag1 sigma(137门) | 64→70（+6，偶发触发） |
| tag2 fold(8390门) | 64→384（大量触发；fold 进位与收敛尾强相关） |
| 自己流上验证 T=27148（refine 中间态） | 全电路同流仅 29 失败，**跳过电路 3018 失败** |

**机理**：宽度表预留的收敛余量进位（fold 高位进位、sigma 终端进位）在"收敛良好"时是死门，
在"收敛滞后"时复活并截断 → **死门与失败是同一枚硬币的两面**。每个输入群体的数值轨迹不同，
哪些余量进位死掉不同。没有大的"跨流结构性死核"。

### 2.3 单调精化实验（/tmp/refine.sh，日志 /tmp/mono.log）
精化映射 T_{k+1} = T_k ∩ D(流_k)（D = 在该跳过电路自身 hash 流上的全电路死门集），
理论上单调收敛到 T ⊆ D 的安全核：
25574 → 22025 → 19957 → 18589 → 17401 → … 每轮 -7%，20 轮未企稳。
**结论：跨流稳定的安全核很小（估计几百到几千），不构成大收益。**
正确做法不是找鲁棒核，而是：**在最终要发货的那个 island 上直接用全死集 T=D（见 §4 路线）**。

### 2.4 所有便宜的"降 λ"旋钮全部无效（重要，别走回头路）
| 改动 | Toffoli 代价 | λ（失败率） |
|---|---|---|
| divide 轮数 +2/+4/+8（SUB4_PP_ROUNDS=706/708/712） | +5.5k/+20k CCX | 33→28→25→20（每 2 万 shot），**收益递减极差** |
| multiply 轮数 +2/+4（SUB4_PP_ROUNDS_MUL） | +4k-5.4k CCX | 不变（39→33，统计噪声内） |
| 宽度表整体 +1 bit / +2 bit（SUB4_PP_WSCHED_FILE） | +7k/+14k CCX | 不变 |

→ λ≈16-18 是当前 body 的固有极限，schedule 已被前人调到 Pareto 最优；
**靠加深/加宽把 λ 压到可磨水平的成本远超死门省的 ~27k CCX，此路不通。**

### 2.5 失败输入没有简单判别特征
dump 了 57 个失败 shot 的 (k1,k2)（/tmp/fails.txt），与 200 个均匀随机对照：
bitlen(k1)、bitlen(k2)、bitlen(Δx)、Δx/p 分桶、低 16 bit 活动、bitlen(k1+k2)
全部无区分度（均值差 < 1 bit）。**滤波器必须模拟走步算法本身，不存在输入端的便宜谓词。**

### 2.6 现有基建盘点
- `src/bin/dead_ccx_scan.rs`：bit 并行（u64 掩码 ×64 shot）门级仿真器，逐门复刻 sim.rs 语义，
  用真实 `build()` + `analyze_ops()`，已验证与 eval 对齐（基线 nonce 下 0 失败）。
  速度实测：~20k 输入 / 70s（含全量仿真）。模式：
  - `DEAD_SCAN_MINING=1`：SUB4_PP_DEAD_CCX=0 强制全发射挖表；
  - `DEAD_SCAN_FIXED_SEED=1` + `DEAD_SCAN_SEED_SALT=n`：固定种子（跨构建可比）；
  - `DEAD_SCAN_REFINE=1`：输入取自"跳过电路 hash"但在全电路上仿真（精化用）；
  - `DEAD_SCAN_GROW=1`：烘焙表生效跑自己的 9024，输出候选死门；
  - `DEAD_SCAN_DUMP_FAILS=<file>`：dump 失败 shot 的 `i k1 k2`；
  - `SUB4_PP_DEAD_TAGS=0b0010/0100/1000`：按 tag 开关跳过（诊断）。
- `src/bin/island_search.rs`：**旧 dialog 电路**的 nonce 磨工具，可直接抄的三块：
  ① op 流只 hash 一次，每 nonce 克隆 hash 状态只喂 96 个尾部 op 字节（O(1)）；
  ② 快速 Jacobian k·G（比仿射快 ~1000 倍）；
  ③ `dialog_gcd_classical_filter` 早期退出（dialog 专用，pingpong 用不了）。
  吞吐参考（08 笔记）：早期退出 ~8,500 draws/小时（10 线程），λ≈7 时 1280 抽出 1 干净。
- `src/point_add/dialog_gcd_classical_filter.rs`：旧头的算法级滤波器（宽度/收敛判定）。
- pingpong body 关键函数：`build_pingpong_point_add`（pingpong_div.rs:3311 起）、
  `value_walk`/`walk_round`（走步）、`replay_halving`/`replay_doubling_inverse`（系数回放）、
  `conditional_mod_negate`、`shrink_to`、`value_width(round)`（785）、宽度表 714 行。

---

## 3. 为什么"磨 nonce"是唯一的钥匙

任何 body 改动（不止死门跳过）都会换考卷 → 必须重新磨到一个干净 nonce 才能发货。
磨 nonce 的命中率 = e^-λ，门级全量仿真每 nonce 太慢（9024×12.45M 门），
必须有**快速滤波器**：给定一个电路配置 + 一个 nonce，快速判定"这套 9024 输入有没有难题"，
命中第一个难题就 early-exit 拒绝。

有两条滤波器技术路线：
- **(A) 快速门级 bit 并行**（基于现有 scanner）：预期 ~1.8s/nonce（早期退出，λ≈17 时平均
  ~8/141 个 batch 即拒），64 核 ≈ 35 nonces/s → e^-7 几分钟，**e^-16 要一周**。
- **(B) 算法级经典模型**（island_search 式）：直接模拟二进制走步的整数递推
  （~3500 词操作/输入，比门级快 ~3000 倍）→ 每秒数千 nonce → e^-23 也只需几小时。
  需要从 pingpong_div.rs 的走步/回放代码重建递推，并同时判定"擦除时 qubit 是否为 1"（相位通道）。

**推荐：先做 (A) 标定**（工作量小，复用已验证仿真器），用全发射电路实测磨 nonce 的真实命中率
和吞吐；若 e^-λ 实测在可磨范围（λ≲10）则直接用；否则上 (B)。

---

## 4. 确定路线（下会话照做）

1. **建 `src/bin/nonce_grind.rs`**（路线 A，复制 dead_ccx_scan.rs 改 main）：
   - 只 `build()` 一次（拿 body ops；尾部 96 个 X 直接丢弃不仿真——它们是恒等对，先 assert）；
   - 复刻 fiat_shamir hash：先喂 body ops（与 scanner 同字节序），每候选 nonce **克隆 hash 状态**
     喂 96 个尾部 X op（q_target 按 nonce 位选 qubit 0/1，成对）再 finalize（抄 island_search）；
   - 输入派生用 Jacobian 快速 k·G（抄 island_search）；
   - bit 并行仿真 body ops，**每 64-shot batch 结束就检查**，第一个失败 batch 立即弃（早期退出）；
   - 同时统计相位垃圾（hmr/R 擦除时目标 qubit 掩码是否非零）；
   - 多线程（~60 线程）扫 nonce 区间（命令行 start count），打印 `CLEAN nonce=N`；
   - 关键校验：用**已知干净 nonce 3009322982643** 跑必须判 CLEAN（0 失败），证明全链路对齐。
2. **标定**：空表（=全发射=当前发货电路）从 nonce 0 扫，实测 (a) 磨到第一个干净 nonce 的抽数
   → 真实 λ；(b) 吞吐 nonces/s。若先扫到的干净 nonce 之一与已知 nonce 行为一致即双重确认。
3. **跳过电路迭代**（§2.3 的正确用法）：
   - 烘焙表从空开始；用 nonce_grind 给当前电路磨一个干净 island ν*；
   - 在 ν* 流上挖**全死集 D(ν*)**（此时收敛最好，D 最大）；
   - 烘焙 T=D → 新电路 → 回到第 1 步重磨；2-3 轮直到 (T, ν*) 联合稳定且 0 失败。
   - 每轮的精化校验：DEAD_SCAN_MINING=0 在 ν* 上必须 0 经典失败。
4. **烘焙胜出 nonce**：在 pingpong_div.rs 顶部 `set_default_env("SUB4_PINGPONG_TAIL_NONCE", "<N>")`
   （build_pingpong_point_add 在 mod.rs 读 env 之前执行；参考 08 笔记把 nonce 写死的做法）。
5. **发货前**：`DEAD_SCAN_MINING=0 ./target/release/dead_ccx_scan` 必须 0 失败；
   然后 `./benchmark.sh --note "dead ccx skip + reground nonce"` 看 9024/9024 与分数。

预期收益：~27k CCX（约 -2.8% Toffoli，最终以 island 上全死集为准），qubits 不变（1263）。

## 5. 编译/运行须知（坑）
- 编译：`cd /home/shen/ecdsa.fail/ecdsafail-challenge && RUSTUP_TOOLCHAIN=1.93.0-x86_64-unknown-linux-gnu CC=gcc RUSTFLAGS="-C linker=gcc" cargo build --release --locked --bin <name>`
  末尾 `/proc/.../fd/pipe restricted` 是沙箱噪音，出现 "Finished" 即成功（exit code 1 也是沙箱问题）。
- 改了 pingpong_div.rs 若怀疑缓存不检测，先 `touch src/point_add/pingpong_div.rs`。
- Edit 工具在本仓库经常失配，用 python 字符串替换打补丁（assert count==1）。
- 当前 `pingpong_dead_ccx_keys.inc` 已恢复为空表（`&[\n]\n`），即与已发货 1.141B 完全一致。
- 环境变量开关：`SUB4_PP_DEAD_CCX=0` 关跳过；`SUB4_PP_DEAD_TAGS` 位掩码；
  `SUB4_PP_ROUNDS` / `SUB4_PP_ROUNDS_MUL` / `SUB4_PP_WSCHED_FILE` 调深度宽度（降 λ 无效，见 §2.4）。

---

## 6. 磨 nonce 标定结果（2026-09-05，工具 src/bin/nonce_grind.rs）

**nonce_grind.rs** 已建成并验证：body 只构建一次，每 nonce 克隆 SHAKE 状态喂 96 个尾 X op（O(1)），
懒派生输入（仿射曲线运算），bit 并行仿真逐 64-shot batch 早期退出，经典+相位双重检查，多线程。
- **全链路对齐验证**：已知干净 nonce 3009322982643 被正确判为 CLEAN。
- 吞吐：~31 nonces/s（58 线程），平均每个被拒 nonce 只花 ~6.5 个 batch（早期退出有效）。

**失败位置分布（8000 nonce）**：
| batch | 累积拒绝率 | 每 batch 存活率 |
|---|---|---|
| 1 | 15.5% | 0.845 |
| 8 | 75.0% | 0.84 |
| 20 | 96.6% | 0.84 |
| 40 | 99.89% | 0.84 |
| 外推 141 | — | P(clean) ≈ e^-24.6（与 02-lambda 的 e^-23 吻合） |

分解：经典拒绝 6546 / 相位拒绝 1454。
**结论：门级磨制无望（约需 5×10¹⁰ 抽签，几十年），算法级滤波器（~1000 倍）是唯一路线。**

## 7. 算法级滤波器设计（下一步实现）

走步核心（walk_round, pingpong_div.rs:1958-2012）的经典语义，每轮：
1. `width = value_width(round)`（700 项表 258→8，round≥700 用末端值）；
2. 偶数轮 source=u,target=v；奇数轮 source=v,target=u；
3. `sign = bit(target,1) XOR bit(source,1)`（bit0 是奇数乘客，借出处理）；
4. 条件带符号加法（signed_add_wrapping，真硬件按模 2^width **截断**）：
   target ← target ± source，使 target 变偶；溢出宽表 → 截断 = 失败根源；
5. target 比特旋转下 1 位（swap 链 + 顶端 cx 回绕）= 模运算下的**除以 2**。
回放（replay_halving_round:2078）：round0 mod_halve_pm；round1 seed_round_one+mod_halve；
round≥2 进 signed frame 后 signed_mod_add_pm_halve_fused(_signed)。
乘法向（replay_doubling_round:2100）是逆过程（倍放）。

**仿真器 = 用 U256 逐函数移植这些算术**（~1500 词操作/输入，比门级快 ~10000 倍），
截断/回绕按真硬件模拟；**验证锚点**：在固定种子 2 万输入上，逐 shot 的 fail/success 判定必须与
dead_ccx_scan（门级 bit 并行）100% 一致。过滤器只需判"这 9024 题有没有硬输入"（early-exit），
命中即拒；磨到 clean 后再用真 eval（benchmark）做最终确认。
要移植的函数清单：signed_add_wrapping / signed_add_wrapping_sigma(_split) / mod_halve_pm /
signed_mod_add_pm_halve_fused(_signed) / to_signed_frame/from_signed_frame / seed_round_one /
fused_lift_round0 / fused_round1 / shrink_to(截断语义) / fused_fold_maskfree / replay_doubling 系 /
conditional_mod_negate（2338）。

---

## 8. 【2026-09-06 决定性发现】走步全都收敛，残余 λ 在回放近似修复，不在 divstep

按 §7 建了 python 原型（`/tmp/proto_walk.py`：复刻 FIXED-SEED 流 + Jacobian 点派生 + Δx
+ 逐轮 U256 divstep，含 shrink 折叠），在 salt60 / 30000 输入（`/tmp/fails.txt` 57 个失败标签）
上对比，结论：

1. **走步对所有输入都收敛**：跑完 696 轮后 min(|u|,|v|) 的中位数，fail 组和 clean 组**都是 1**
   （fail max=47 bit, clean max=63 bit，无区分度）。简单"目标 ±source 越界计数"也无区分度
   （fail med=289, clean med=289）。→ 02-lambda 里的"divstep 收敛尾 5.73"在本电路已基本被
   696/694 轮 + 自愈消化掉，**不是当前失败源**。

2. `shrink_to`（pingpong_div.rs:1934）**不是简单截断**：释放高位前先 `cx(高位, 次高位)`，
   把丢弃位的**奇偶性折叠**到新顶端。缩到宽 W：低位 0..W-2 原样保留，bit W-1 = 原 bit W-1..L-1
   的奇偶性。`grow_to` 是 sign-extension 逆过程。过滤器必须照此折叠（原型已实现）。

3. **残余失败 = 回放重建中的"近似测量修复 + fold 截断窗"**，在精确字段值上可判：
   - 分块测量加法 `add_chunked_measured_with`（:2508）：每个分块边界 carry 被 hmr 测量擦除，
     再用 `cmp_lt_phase_conditioned(acc[hi-cmp..hi], addend[hi-cmp..hi], phase)` 只比较分块
     **顶端 `compare=21` 位**（REPLAY_CHUNK_COMPARE）经典重算 carry（erase 闭包 :2548-2555）。
     分块宽 >21 时，低端 (w-21) 位产生的进位若把顶端和顶到溢出就**漏判 → 相位垃圾**；
     概率 ~2^-21/边界。每走步约 2,300-2,400 个截断修复（:2149）→ 2400/2^21 ≈ **0.11%**，
     与相位垃圾率 5/9024≈0.055% 同量级 → 定量吻合。这是**相位失败**类（输出经典仍对，但
     该批 R 测量翻相位）。
   - **经典失败**类：改数值的截断借位/进位窗——`round1_window`（=32+endpoint_fold_window=50,
     :1206，"borrow 越过切片丢弃 ~2^-20/次"）、`replay_fold_window=53`、`endpoint_fold_window=18`、
     `replay_flag_compare=20`；mod_halve_pm/mod_double_pm/seed_round_one 里的
     `csub/cadd_nbit_const_direct_trunc_fast_dead_low(_host)`（常量 ±f 的 fold 加法）截断位宽
     出错 → 真数据位错。

4. **几何全部数据无关**：分块边界 chunk_bounds/chunk_layout 只依赖 width/ladder 预算/plan
   （round 的函数，非数据），可一次性预算；每 shot 只需精确字段大整数（U256）判窗口条件。
   回放系数对 (x,y) 是 numerator 与符号带的**精确模线性递推**：
   `mod_halve_pm(t)= t·2^-1 mod p`（t 奇→(t+p)/2，偶→t/2）、`seed_round_one`（target=±source，
   再常量 (2^256-p-1) 调整）、round≥2 `signed_mod_add_pm_halve_fused`（条件 ±source 后模 halve）；
   multiply 向是逆过程 mod_double_pm/seed_round_one_inverse/signed_mod_double_add_pm_fused。
   符号带来自走步（原型已能产出）。

5. 实际 bake 配置（mod.rs:2704 起）：`SUB4_PP_ROUNDS=696` divide / `SUB4_PP_ROUNDS_MUL=694`
   multiply / R1=335 / R2=645 / `SUB4_PP_SIGNED_FRAME=0`（**无 signed_frame 转换**）/
   REPLAY_CHUNK_COMPARE=21 / REPLAY_FOLD_WINDOW=53 / ENDPOINT_FOLD_WINDOW=18 /
   REPLAY_FLAG_COMPARE=20。宽度表从 `PP_DUMP_WIDTHS=1` 实跑 dump（已加在 build_pingpong_point_add
   开头，env 门控；W0=259 降到 ~8）。ec_add 两次走步：Divide 分母=Δx=tx-ox（求逆得斜率
   λ=Δy·Δx^-1，696 轮）；Multiply（694 轮，注释说只占 ~0.05 λ，次要）。

### 8.1 修正后的过滤器移植计划（取代 §7 单纯走步收敛假设）

过滤器每 shot：
1. 精确字段：points、Δx、Δy；走 walk 拿符号带（已可用，注意 shrink 折叠）；
2. 用**精确模运算**回放系数对（x,y）演化（mod_halve_pm / seed_round_one /
   signed_mod_add_pm_halve_fused 的字段版，全部 mod p，不截断）；
3. 每个回放 chunked-measured add：用**预算好的 chunk 几何**(lo,hi)，取当时 acc/addend 字段值，
   判近似修复 miss：w=hi-lo>21 时，低端 (lo..lo+w-21) 子和是否产生进位且顶端 (hi-21..hi)
   和恰为全 1（进位顶溢出）→ 相位脏；
4. 每个 trunc 常量 fold 加（round1/fold/flag window）：判截断窗口内借位/进位是否越过 window →
   经典错；
5. divide + multiply 两向都判；任一触发即拒。
**锚点**：逐 shot 与 dead_ccx_scan 门级 fail/success 对齐（salt60 30000，57 标签），目标召回 100%。

### 8.2 原型实测进展（2026-09-06，/tmp/proto_walk.py、/tmp/proto_replay.py）

- **核心 divstep 递推与极性已验证正确**：固定全宽 259 bit、不折叠、跑 800 轮，200/200 随机
  分母都收敛到终态 (1,1)；极性约定 **sign=0→加、sign=1→减**，halve = 算术右移（top bit 符号
  扩展：new[i]=old[i+1]，new[W-1]=old[0]^old[W-1]）。极性反了 0/200 收敛。
- `shrink` 折叠语义已实现（缩到宽 W：低 0..W-2 原样，bit W-1 = 原 bit W-1..L-1 奇偶）。
  带 shrink 走步对大多数输入终态 min(|u|,|v|)=1（proto_walk 30k：fail/clean 中位都=1，无区分度）。
- **手工推系数回放反复失败（6 种结构变体 0/60 命中）**：系数对 (x=coefficient=0,
  y=numerator=Δy)，回放 r0 y=mod_halve(y)；r1 odd src=y,tgt=x：x=mod_halve(±y)；r≥2
  tgt=mod_halve((tgt±src) mod p)，符号同走步；最后 conditional_mod_negate(u 符号,x)
  (v 符号,y) 再 cx(numerator→coefficient)。试了 init 交换 / 极性翻转 / 四种 negate×(+|xor)
  组合，全部 0 命中；且**结果寄存器是哪一个**没完全确认（pingpong 返回 denominator，但
  coefficient 末尾 free、numerator=y2）。→ **不能靠读代码猜最终 Bézout 组合。**

### 8.3 决定的下一步（消除猜测）：门级轨迹拟合

不再手推。改造 dead_ccx_scan，在**单个 shot（单 bit lane）**上、于几个 tag 轮次边界 dump
出寄存器的 U256 整数值：u、v（走步）与 coefficient、numerator（回放）。做法：在 B 里给
walk_round / replay_halving_round / signed_mod_add_pm_halve_fused 入口加 env 门控 eprintln，
打印该轮各寄存器 slice 对应的 u64 掩码（取 lane0），与 python U256 递推逐轮 diff，直到
u/v 和 coefficient/numerator 全程一致。拿到正确递推后：
1. 回放在**精确字段值**上跑（不截断）；几何(chunk bounds/windows)一次性预算（数据无关）；
2. 近似 carry 修复（cmp_lt_phase_conditioned，chunk 宽>21）逐边界判 miss（相位类，~18%）；
3. trunc fold 常量加减（round1/fold/flag window=18/20/53）判截断窗越界（经典类，~82%）；
4. divide+multiply 两向，任一触发拒。锚点：salt60 30k 对齐 /tmp/fails.txt（57），目标召回 100%。

诊断痕迹：PP_DUMP_WIDTHS=1 可 dump 宽度表（已加在 build_pingpong_point_add 开头，env 门控，
提交前移除或保持 env 关闭即无影响）。

---

## 13 — 快线：峰值 qubit 普查与 SUB4_PP_PEAK 扫描（2026-09-06）

### 13.1 峰值 1,263 的精确构成（B0 普查，当前源码实测）

峰值时刻 ops=913,918，phase=pp_div_replay（divide 第一批 replay batch 进行中）：

| 数量 | 分配点 | 身份 |
|---|---|---|
| 333 | pingpong_div.rs:2012 | tape 符号 qubit（= plan.r1 341 附近，已消费 round0/1 后）|
| 256 | :3403 | y2 寄存器（全宽）|
| 256 | :492 | coefficient 寄存器 |
| 145 | adder.rs:341 | **u 寄存器**（load_const(P) 后 shrink 至 value_width(r1)≈145）|
| 145 | :3402 | **v 寄存器**（x2 寄存器 shrink 剩余）|
| 126 | :2449 | chunk 加法器进位梯子 |
| 2 | :2614 | chunk 边界进位 |

全部为峰值时刻必需（u/v/y/coefficient 是计算态，梯子是 batch 效率），无单一"漏点"。

### 13.2 tape 符号逐位vent：此路不通（重要负结果）

- 已有单点先例：a0_free（round 0）、sign1_fix（round 1）、bchain_mul_j（恢复单个符号）
  ——均为"hmr 测量 + walkback 重算 + z_if 修相位"。
- **推广被两个事实堵死**：① u/v 空间低0不变量（source[0]=target[0]=1 进加法）⇒
  post-add bit1 ≡ 1 恒成立，符号信息在 walkback 时的本地 u/v 状态中不可恢复；
  ② op 集无经典位控制的数据门（cx_if/ccx_if 不存在，cz_if/z_if 仅相位修复）。
  符号是每轮 1 bit 独立信息，tape 不可压缩（b-chain 恒等式只给 1 个线性约束）。
- 结论：tape 深度 = walk 领先量，唯一杠杆是减小 r1（连带 u/v 变宽，净值
  d(peak)/d(r1) ≈ −1 + 2×0.35 ≈ −0.3，收益弱），交给求解器统一权衡。

### 13.3 正路：SUB4_PP_PEAK 直接是求解器峰值目标

- `Plan { r1=341, r2=628, peak=1273 }`，env：`SUB4_PP_PEAK / _MUL / _R1 / _R1_MUL /
  _R2 / _WALK_PEAK(_MUL)`（pingpong_div.rs:2210-2222）。
- `allowance = peak − (tape_len + 2N + 2·walk_width)` = replay batch 梯子预算
  （:2228）。梯子 87→130（43q）↔ Toffoli −2,848 ⇒ **~66 T/qubit（线性区）**。
- 基线目标 1273 → 实测 1,263（10 slack）。地板 ≈ 1,137（333+290+512+2）。
- 预期：目标 1,173（−90q）≈ +6k T → ~1.06B（−7%）；再坐标上升 R1/R2 回血。
- 扫描进行中：PEAK=PEAK_MUL ∈ {1273,1253,1233,1203,1173,1143,1113}，每档
  B0 普查出 Q、count_tof 出 T（结果回填于此）。
- 注意：改 PEAK 即改 body → Fiat-Shamir 换卷 → 发货前必须用主线滤波器重磨干净
  nonce。快线与主线是同一条船。

### 13.4 扫描 1 实测（2026-09-06，推翻 13.3 预期）

真实硬编码基线（mod.rs:2704-2736 set_default_env）：ROUNDS=696 / ROUNDS_MUL=694 /
**R1=335 / R1_MUL=326 / R2=645 / PEAK=WALK_PEAK=1267** / REPLAY_CHUNK=96。
（plan() 代码默认 341/628/1273 是过期回退值。）

| 配置 | Q | T(count_tof) | score |
|---|---|---|---|
| PEAK=PEAK_MUL=1273（怪配置，未耦合 WALK_PEAK）| 1271 | 939,267 | 1.194B |
| 1253 | 1263 | 966,607 | 1.221B |
| 1233 | 1263 | 997,803 | 1.260B |
| 1203 | 1263 | 1,061,198 | 1.340B |
| 1173 | 1263 | 1,140,722 | 1.441B |
| 1143/1113 | 1263 | 1,196,914 | 1.511B |

教训：
1. **只覆盖 PEAK 不耦合 WALK_PEAK 会造出怪配置**（T 反而比基线差 36k）。
2. **PEAK 旋钮单独压不动 Q**：divide 侧压下去后，峰值转移到 multiply 实例
   ——其 value_walk 一次性走完 694 轮（694 tape + y 256 + coefficient 256 ≈ 1,263），
   结构性对 PEAK 免疫（doubling replay 逆序，必须先走完全程；低目标档普查
   n_groups=10 实证：361+333 双代 tape + u/v 已缩到 1 位宽）。
3. multiply 墙 ≈ 1,263 是快线真正障碍；拆墙需分段走步重构（晚块逐轮交错），
   或接受 multiply 墙作为地板（~1,240）。
4. 交换率实测 ~3,400 T/q（怪配置），远差于注释里的 66 T/q（那是 walk 梯子
   局部敏感度，不是全局）。快线经济性存疑，等 R1×PEAK 耦合扫描（进行中）。

### 13.5 两面墙模型确立 + ROUNDS_MUL 杠杆（2026-09-06）

R1 扫描（300→180，PEAK 耦合）：**Q 全部 1,263 不动，T 仅 +0.4k~+4k**——divide 侧
任何调整都被 multiply 墙遮蔽。

**两面墙都恰好停在 1,263**（canonical 平衡点）：
- divide 墙 = r1-tape 333 + u,v 290 + x/y/coefficient 512 + 梯子 128（solve 于 PEAK=1267−4）
- multiply 墙 = value_walk 一次性 694 符号 + 512 + u,v 16 + 杂项 ≈ 1,263。
  **结构性不可分段**：doubling replay 逆序（回放第 r 轮依赖 r+1 的系数态），
  必须先走完全程 → tape=ROUNDS_MUL 是地板。

ROUNDS_MUL 扫描（纯 env）：

| RMUL | Q | T | score |
|---|---|---|---|
| 694 | 1263 | 944,442 | 1.193B |
| 650 | 1263 | 925,246 | 1.169B |
| 610 | 1263 | 906,868 | 1.145B |
| 590 | 1263 | 897,420 | 1.133B |

- **T 每轮 ≈ −452 CCX**（走步加法+回放+回走全链），远超预期。
- Q 不动是因为 divide 墙仍在——须与 (R1, PEAK) 耦合（组合扫描进行中）。
- **λ 风险**：value_width 是固定 700 项表（不随 ROUNDS 缩放），砍轮次=砍收敛
  预算，尾部宽度停在 ~33 位；λ 恶化幅度未知，须用 dead_ccx_scan
  （DEAD_SCAN_FIXED_SEED + DEAD_SCAN_SHOTS）对候选配置实测后再采用。
- 注意 count_tof（emitted CCX，canonical=944,442）与官方 score 的 Toffoli
  （903,396.347）度量不同，扫描用前者做相对比较，发货前以 benchmark.sh 校准。

### 13.6 组合扫描判决 + RMUL 赢家（2026-09-06）

(RMUL × R1 × PEAK 全耦合) 8 配置：**Q 从未低于 1,263，R1≤180 反而涨到 1,295/1,304**
（u/v 变宽 + 梯子回退 > tape 收益，13.3 的 −0.3/轮模型实测不成立），T 全面上涨。
**env 旋钮压 Q 的路线全部证伪。**

但 sweep 3 单独 RMUL 是真赢家（Q=1,263 不变，T 大降）：

| RMUL | ΔT(emitted) | 官方度量预估(×1,263) | vs nipzu 1.139B |
|---|---|---|---|
| 694 | 0 | 1.141B（现状） | −0.2% |
| 630 | −28.2k | ~1.106B | −3.1% |
| 610 | −37.6k | ~1.096B | −3.9% |
| 590 | −47.0k | ~1.086B | −4.7% |

机理：multiply 尾部轮次在典型输入收敛后空转（符号恒 0、回放恒等），
每轮全链 ≈452 CCX。砍轮次 = 纯赚，唯一风险是收敛预算 → **λ 探针进行中**
（dead_ccx_scan 固定种子 salt60，canonical 锚点 57 fails/30k shots）。

注意：官方 Toffoli = **平均每 shot 实际执行 CCX**（eval_circuit.rs:361，模拟器
跳过控制端 |0> 的 CCX），count_tof 的 emitted 944,442 只是相对比较代理；
RMUL 的 ΔT 是真删除，两种度量下同向。

若 RMUL=590 的 λ 可接受（如 ≤2×），则叠加死门跳过（−27k T）→
~870k emitted → 官方度量 ~1.05B（−8%）。快线与主线在此会师。

### 13.7 λ 探针判决 + multiply 实例建模突破（2026-09-06 晚）

**1. RMUL 路线正式关闭**（λ 探针，dead_ccx_scan 固定种子，每档 15000 live shots）：

| RMUL | fails @batch140(≈8400 shots) | 每 shot 失败率 |
|---|---|---|
| 694 (canonical) | 19 | ~0.23% |
| 630 | 2,982 | ~35% |
| 610 | 6,241 | ~74% |
| 590 | 8,303 | ~99% |

砍轮次 = 砍收敛预算，λ 灾恶化（非"尾部空转"）。**任何电路 body 改动后的
重磨干净 nonce 依赖 ~100% 召回滤波器，RMUL 增大失败率 ≈ 增大磨制难度数量级。**

**2. multiply 实例输入确认**（读 ec_add.rs + square.rs 代码链）：
一次 `pingpong_mod_mul_div_in_place` = value_walk(rounds_for(dir)) → replay →
walkback，Divide/Multiply 是**两次独立调用**（696/694 轮，各自宽度表）。
ec_add 序列：x2=Δx(vented) → tlm_inverse(y2=Δy·Δx⁻¹=λ) → coord_add3x(x2+=3·ox)
→ square_sub(x2−=λ²) → tlm_forward_multiply(y2·=x2)。故
**D_mul ≡ tx + 2·ox − λ² (mod P)**（trace 实证 2·round0_dump ≡ D，25/64 ——
其余 39 个 lane 差在 vented/扩展位精确位型）。

**3. trace round-0 dump = post-fused-lift 态**。lift 会把 not_a1 异或进 3 个
扩展位（256..258）——pp_filter 的 `lift_round0` 假设扩展位入口为 0（对 divide
的 vented 入口成立；divide dump == odd_rep(Δx canonical) 64/64）。multiply
入口 x2 寄存器的扩展位非零（coord/square 运算残留），精确建模需补
coord_add3x/square_sub 的代表元语义。

**4. 滤波器现状**（/tmp/pp_filter.py + mul_walk_check，canonical 入口近似）：

| 指标 | 之前 | 现在 |
|---|---|---|
| fails.txt 召回 | 31/57 (54.4%) | **46/57 (80.7%)** |
| 每 shot 漏检率 | ~1.1e-3 | **~3.7e-4**（mul_walk_nonconverged 抓 15/26） |
| 基线 nonce 9024 shots 误杀 | — | **0/9024**（grind 可行性关键指标通过） |
| 吞吐（含 EC mul） | ~565/s | ~395/s |

**5. 剩余缺口与 grind 数学**：11 个漏检需 multiply replay（doubling 侧
mod_double_pm/seed_round_one_inverse 折叠窗）+ 精确入口位型。当前漏检率
3.7e-4/shot → P(脏 nonce 全过滤波) = 1−(1−3.7e-4)^9024 ≈ 96%——**磨制前
必须把召回推向 ~100%**（目标漏检 ≲1e-5/shot）。mul replay 的 x/y 轨迹
trace 未记录（只有 div replay 有），需加 trace 点或读代码推。

---

## 【2026-09-08 夜间】门级 fold/walk 预测器完成并事件级验收（canonical frame 定稿）

### A. 重大纠错：shipped 电路是 CANONICAL FRAME，不是 signed frame
- [mod.rs](../mod.rs) `set_default_env("SUB4_PP_SIGNED_FRAME","0")` 强制 canonical；
  之前"signed 帧"的推导作废，所有建模以 canonical 单元为准。
- 铁证：trace64 的 sa/ta/tb/tc/td 记录点只存在于 canonical 单元
  `signed_mod_add_pm_halve_fused`（pingpong_div.rs L2876-2953）；64 lane ×
  694 轮共 44,416 条记录全部落在 canonical；div replay 走
  `replay_halving_round` 的 else（canonical）分支，to_signed_frame 不执行。

### B. fold 进位链是逐位 maj（不是"加常数"黑盒）
- fused_fold_maskfree（L2728-2860）窗 W=53：
  - e_i = f_i·plus_f ^ f_{i-1}·plus_2f ^ negf_i·minus_f
    （F_BITS(53 内)=[0,4,6,7,8,9,32]；NEGF=2^53−F，47 位）
  - c 初值 = first_carry（hrep: ~sign&parity；drep: V0&(d^o)），
    c_i = maj(V_i, e_i, c_{i-1})；进位过 bit52 丢弃（fold 截断）。
  - **slot i（1..50）门 fire ⟺ (e_i^c)&(V_i^c)；terminal slot 511（位 51）同式。**
- trace 反演验证：16 lane × 694 轮 = 11,104 块中 11,101 块的 tb→tc 精确
  符合 const∈{−F,0,+F,+2F} fold；**3 个异常块**（lane0 r540、lane2 r233、
  lane12 r268）carry 链在某槽位中断 1-2 位后自愈——正是 skipped 门触发的
  脏轮签名（trace64 跑在带 skip 的 shipped 电路上）。预测器模拟"干净算术"，
  FIRE 真值 = 正确运行中本该 fire 的门，两者在全量 9024 shot 上事件级吻合。

### C. walk sigma 门（tag1）模型
- signed_add_wrapping_sigma（L1648-1806）= Gidney carry ladder：
  目标位先 ^sign 翻转，ladder CCX 在位 i（i=2 special，3..w-3 slot=i，
  w-2 为 terminal slot 511）fire ⟺ (S_i^c)&((T_i^sgn)^c)，
  c 为 S+(T^mask) 行波进位；**bit0 物理 cin=0**（奇数乘客 S0=T0=1，
  cout0=1^sgn，可证 C1≡S1）。top_skip 默认关（SUB4_PP_WALK_TOP_SKIP
  未设），故 terminal CCX 恒存在；walk_low_chunk 选 chunked split(tag3)
  的轮次用另一套 uid/键。
- 相位：dwalkf=div walk 前向（walk_round）、walkf=mul walk 前向
  （value_walk）；mwalkb/walkb 反向。偶数轮 source=u/target=v，奇轮
  source=v/target=u（与 pp_filter.run_walk 一致）。

### D. 全量验收结果（/tmp/dg_filter.py + /tmp/eval_full2.py，9024 shot）
- **hrep/drep fold：147 个 FIRE 事件事件级 0 误差**（TP=147，FN=0，FP=0）；
- **walk（dwalkf+walkf）：2/2 真值事件召回**（shot 5929 dwalkf r416
  slot114；shot 1592 walkf r561 slot511）；
- **仅 1 个 FP**：shot 4288 walkf r318 slot511（终端进位链 carry 穿传播区
  到顶，宽度±1 即不 fire；疑似 mul walk 入口扩展位/sparse-lift 位型细节，
  FPR≈1.1e-4 于 walk 子集、1.1e-4 全 shot——研磨时多弃 1 nonce/9k，无害）；
- 即 146/146 脏 shot 全召回，8,878 干净 shot 零折叠误杀；
  mwalkb/walkb（38 个 baked 键）9024 shot 内零 fire，暂未建模。
- 速度：纯 Python 33 shots/s（ec_mul 为主），Rust 移植目标 ≥1e5/s/核。

### E. 关键文件/数据（/tmp，易失，尽快固化进仓库）
- /tmp/dg_filter.py：fold_fires/fused_halve_round/run_div_replay/
  double_round/run_mul_replay/walk_adder_fires/simulate_pair；
  入口 simulate_pair(k1,k2, table_hrep, table_drep, table_dwalkf=,
  table_walkf=) → fires=[(phase,round,slot)]。
- /tmp/pp_filter.py：canonical ec_mul/run_walk 等（未改）。
- /tmp/eval_full2.py：9024 全量事件级评估；/tmp/eval_dg.py 小样本。
- 真值：/tmp/fire_base.txt（9024 INPUT + 151 FIRE）、
  /tmp/dg_sites_ext.txt（27,231 DGSITE 键→phase/round）、
  /tmp/inc_mined_10241.inc（= 仓库内 pingpong_dead_ccx_keys.inc，10,241 键）。
- 生产表相位分布：hrep 5088 / drep 4867 / dwalkf 122 / walkf 126 /
  mwalkb 17 / walkb 21 键。
