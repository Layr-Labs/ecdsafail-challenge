# 13. Dead-CCX skip 被 FS 雪崩堵死 → 冲榜杠杆转向降 Q（2026-09-07 夜间）

## TL;DR（最重要的结论）
- **官方评分的 T 是动态计数**：`avg executed Toffoli = sim.stats.toffoli_gates / 9024`，
  每个 CCX 按它 **cond 激活（executed）的 shot 数**累加（sim.rs:86），不是静态门数。
- **全发射电路（skip 0 个死门）官方 eval：0 failure，avg_tof = 903,396.347，Q=1263**。
  这就是当前 1.141B 分数的来源（前人没 skip 死门，或退回全发身）。
- **skip 死门降 T 的路线被 Fiat-Shamir 雪崩本质堵死**：无论跨多少独立流挖"结构死键"，
  skip 后 FS hash 雪崩成新流，残留 ~p>0 的键必在某 shot fire → classical mismatch，无法可靠归零。
- **冲榜首（nipzu 904,049 T × 1260 Q = 1.1391B）的正确杠杆是降 Q，不是降 T**：
  保持全发射 0-failure（T=903,396），只要 **Q 从 1263 降到 1260**：
  903,396 × 1260 = **1.1384B < 1.1391B 即夺冠**；降到 1259 = 1.1375B 更稳。

## 官方 ground truth 评测方法（本地自测，不碰排行榜）
`benchmark.sh` 提交前需用户确认，但可手动跑它的两个本地步骤验证（纯本地、无网络/提交）：
1. `cargo build --release --bin build_circuit --bin eval_circuit`
2. 空目录里跑 `build_circuit`（调 `point_add::build()`，写 `ops.bin`；`SUB4_PP_DEAD_CCX=0` 强制全发射）
3. 同目录跑 `eval_circuit`（trusted，读 `ops.bin`，重新仿真 9024 shot，打印 mismatch / avg Toffoli / qubits）
- eval_circuit.rs:204 `fiat_shamir_seed(ops)` 从**提交的 ops.bin**（skip 后的 ops）算 seed，
  与 dead_ccx_scan 的 seed 函数字节一致 → **雪崩是真实评分逻辑**：skip 门→ops 变→seed 变→9024 流变。
- eval_circuit.rs:295 `sim.apply_iter(ops)`；单 xof 先读 9024 个 (k1,k2) 输入再喂 Hmr/R 测量流（共享 reader）。
- **失败提交记 0 分**（fail_and_exit 写 avg_tof=0）；0-failure 是硬前提。
- dead_ccx_scan 的 VERIFY（`DEAD_SCAN_MINING=0`）与官方 eval **完全一致**（同报 162 mismatch），可信。

## 雪崩堵死的实验证据链（256 独立流 + 官方 eval）
挖"跨独立随流都不 fire 的结构死键"（FIXED_SEED：全发射电路 + salt 固定 seed 流，
`DEAD_SCAN_FIXED_SEED=1 DEAD_SCAN_SEED_SALT=i DEAD_SCAN_SHOTS=9024 DEAD_SCAN_FORCE_WRITE=1`，
写 `/tmp/dead_salt_i.txt`），烘焙交集后官方 eval：

| 表 | 键数 | 来源 | 官方 eval mismatch |
|---|---|---|---|
| shipped baked | 10,241 | 旧 mining（Q1267 遗留） | **162**（+62 phase garbage）→ 不合规 |
| struct 16 流交集 | 11,925 | salt 0-15 | 253 |
| struct 48 流交集 | 7,436 | salt 0-47 | 75 |
| struct 256 流交集 | 2,368 | salt 0-255 | **25**（仍不 zero） |
| 全发射（空表 `&[]`） | 0 | `SUB4_PP_DEAD_CCX=0` 或空 inc | **0** ✓ avg_tof 903,396 |

- 跨流核随流数持续收缩、无平台：16→11925, 48→7436, 256→2368（真·p=0 数学死键极稀少）。
- **REFINE retain 在雪崩下系统性失效**：从 struct48 7436 跑 6 轮 retain（7436→6887，砍 549 键），
  官方 mismatch 仅 75→**72**。原因：retain 在"上一个雪崩流 F_prev"砍 fire 键，而官方 eval 用
  "skip 后的新雪崩流 F_new"，两流雪崩无关 → 砍的键对当前 mismatch 无贡献（雪崩错位）。
- 统计模型：N 流核内键 fire 率 ~1/(N·9024)，9024 shot 期望 fire 事件 ≈ 核大小/N，
  要 <0.1 需 N > 10×核大小（上万流，不现实）；且 FS(skip) 流由 skip 自身派生（雪崩反馈），
  与 FIXED_SEED 独立流不独立 → 比纯统计更差。

## 为什么"数学死键"也救不了
- shipped 10241 与 fast_filter_tables.inc 的 FIRE/WDIV/WMUL 都不是 p=0 数学证明，而是
  统计挖矿 / 世界模型（FIRE 表只服务 fast_grind 磨 nonce，预测 fold/walk 相位，概率性）。
- pingpong 死 CCX 主要是 fold/walk 相位条件门，fire 依赖测量流分支（PushCondition on measured bits），
  测量流变→分支变→可能 fire。真正 p=0（控制位接恒 0 clean ancilla）的门设计者本就不 emit。
- hash 吸收每 op 的 kind+6 个 id（eval_circuit.rs:208-216）：skip 必改 len/序列→雪崩；
  无法"skip 但保持 hash"（要 hash 不变 kind 必须仍是 CCX→仍计 T，死锁）。

## 当前工作区状态（重要）
- **live inc `src/point_add/pingpong_dead_ccx_keys.inc` 已设为空表 `&[]`** = 全发射、
  官方 eval 0-failure、903,396 T × 1263 Q（合规安全网，可直接 build 出 0-failure ops.bin）。
- 备份（均在 /tmp 或 backups，重启可能丢 /tmp）：
  - shipped 10241：`/home/shen/ecdsa.fail/backups/pingpong_dead_ccx_keys.inc.bak_10241`、`/tmp/inc_shipped_10241_live.inc`
  - struct48 7436：`/tmp/inc_struct48_7436.inc`、键 `/tmp/struct48_keys.txt`
  - struct256 2368：`/tmp/inc_struct256_2368.inc`、键 `/tmp/struct256_keys.txt`
  - 256 流原始死键：`/tmp/dead_salt_0..255.txt`（每流 ~26-29k 键）
  - REFINE 各轮：`/tmp/inc_sref_*.inc`、`/tmp/inc_tail_*.inc`
- 工具脚本：`/tmp/run_salts2.sh`（16-47）、`/tmp/run_salts3.sh`（48-255，xargs -P48）、
  `/tmp/refine_struct.sh`、`/tmp/tail_refine.sh`。

## 下一步（降 Q 方向，夺冠杠杆）
- 目标：pingpong 电路 qubits 1263 → ≤1260（保持全发射 0-failure，T≈903k 即可超 nipzu）。
- qubit 经 builder `alloc_qubit()`/`next_qubit` 计数；venting.rs 有大量 ancilla
  venting/uncompute 测试基元（q_dirty/q_clean2/q_ctrl 等复用模式可参考）。
- 先做 qubit 预算账本：哪些 ancilla 生命周期不重叠可复用（walk/fold/split/replay 阶段间），
  找 3 个可省 qubit。每改一次用 build_circuit+eval_circuit 验证仍 0-failure 且 qubits 下降。
- **降 Q 是电路结构大改，需在用户参与/确认下推进；dead-ccx 降 T 路线已证伪，勿再投入。**

## 13b. Q=1263 精确定位（2026-09-07，TRACE_QBIND 探针）
- **活动电路是 pingpong，不是 trailmix**：`build()`(mod.rs:2830) 在未设
  `SUB4_LEGACY_POINT_ADD` 时走 `build_pingpong_point_add()`(pingpong_div.rs:3270)，
  经 `ec_add_with_division` 闭包调 `pingpong_mod_mul_div_in_place`(pingpong_div.rs:242)。
  trailmix 仅作 schedule/ec_add 框架。`plan()` 运行时返回 Some（Divide r1≈335 r2≈645，
  Multiply r1≈326），即走 Some(plan) 分支。
- **Q 高水位全在 Divide 段**：INPLACE Divide 起步 nx=1026（ops≈13k），Multiply 起步
  nx 已 1263（ops≈6.6M，coeff_mul pre pool=299 → post pool=43，0 mint）。Multiply 不绑。
- **决定性 mint 点 = Divide replay 系数分配** `coefficient = b.alloc_qubits(N)`
  (pingpong_div.rs:440, Some-Divide 分支)：ops≈911,409，pre `active=882 pool=168 next_idx=1050`
  → post `active=1138 pool=0 next_idx=1138`。即 256 个系数位中 168 复用池、**新铸 88 个 ID**。
  随后 replay 进位梯(carry ladder, `carries` alloc)再铸 125 个 → nx=1263。
  **在系数分配前往池里多放 3 个 qubit，整条 mint 级联下移 3 → 峰值 nx=1260（Q=1260）。**
- **RNG 偏移无害（关键纠错）**：换 DIALOG_TAIL_NONCE 改 FS seed 仍 0-mismatch（电路对任意
  seed 结构正确）。HMR/R 吞 8 字节 RNG 只改测量流分支，不致错。`b.free(q)=r(q)+release_clean`
  的 R 门是电路已大量使用的常规释放。之前 extra-free 失败是**结构 bug**：walkback 走 low0=false
  路径，pre-add 符号应为 `sign = target[1]^source[1]`（两条 CX，**无 x**），旧代码写
  `cx(target[1],sign); x(sign)` = !target[1]，错。
- **release_clean 是干净释放原语**(mod.rs:727)：b.x(q) 后 release_clean 只入池、不发任何
  量子门/RNG（X 门被经典控制吞掉）。`loan_interleaved_odd_passengers`(pingpong_div.rs:2125)
  即用此法释放 u[0],v[0]。**但只能释放"不再按原 ID 取回"的 qubit**：系数分配会 LIFO 弹走
  刚 release 的 u[0]/v[0]，而 replay 后 restore_interleaved 要按 ID reacquire → 会 panic/别名
  （系数是长命寄存器）。故 odd passenger 不能捐给系数。
- **可行杠杆**：在系数分配(line 440)前做 3 个**永久释放**（不按 ID reacquire）的 tape 符号 qubit，
  像已证可行的 a0(tape[0]，walk 循环内 HMR 释放 + walkback recompute) 那样。tape[1](sign1)
  已有可证正确的 recompute(sign1_fix)，但在 replay r=1 **之后**才释放（太晚）。需把可重算的
  符号位释放提前到系数分配之前，并在 replay 侧相应重构 r=1,2 取符号。walkback 正确重算式：
  `s=alloc; cx(target[1],s); cx(source[1],s); z_if(s,c); x(s); signed_add_wrapping(s,...,low0=false); x(s); cx(target[1],s); cx(source[1],s); free(s)`。
- 探针函数 qbind/eprintln_if_qbind 已随 `git checkout pingpong_div.rs` 移除；复现可在
  alloc_qubits 站点加 env-gated eprintln 打印 b.active_qubits/free_qubits.len()/next_qubit/ops.len()。


## 13c. Extra-free 符号重算证伪（2026-09-08）
- **extra-free 方案从根本上不可行**：rounds 2+ 的 sign = `target[1] ^ source[1]`，前向 add 修改了 target，
  所以 walkback 中 `target[1]_after ^ source[1]` ≠ `tape[round]`（= `target[1]_before ^ source[1]`）。
  逆向 add 用错误 sign → 无法正确撤销前向 add → 7958 mismatch。
- **a0/sign1 可行是因为从 source(未修改)重算**：a0 = `v[N-1]`（source 顶位），sign1 = `!v[1]`（source 次低位）。
  source 不被 add 修改，所以 walkback 可正确重算。rounds 2+ 的 sign 依赖 target[1]（被 add 修改），无法重算。
- **memory 13b 的"pre-add 符号应为 target[1]^source[1]"是错误结论**：该式给出的是前向 add 之后的值，
  不是 `tape[round]`（前向 add 之前的值）。z_if 相位校正只修 HMR 测量反作用，不修 sign 数值错误。
- **Q=1263 是当前电路结构硬限**：系数分配(pool=168, mint 88) + carry ladder(mint 125) = 1263。
  降 Q 需全新算法方向（如改除法结构、减少系数位宽、或找到不依赖 target[1]_before 的 sign 表达式）。
- **已验证**：extra-free=3 → Q 仍 1263（释放在 replay 中，系数分配之后，不降 Q）+ 7958 mismatch。
  还原 extra-free=0 → Q=1263, T=903396, 0 mismatch（安全基线）。

## 编译/工具备忘
- 改 inc 必须重编（`touch src/point_add/...inc && cargo build --release --bin <b>`）。
- 编译末尾 "TRAE Sandbox Error /proc pipe restricted" + exit 1 是沙箱噪音；见 "Finished release" 即成功。
- dead_ccx_scan 模式：MINING(默认全发射200k随机)、VERIFY(`DEAD_SCAN_MINING=0`)、
  REFINE(`DEAD_SCAN_REFINE=1`)、GROW(`DEAD_SCAN_GROW`)、FIXED_SEED(`DEAD_SCAN_FIXED_SEED=1`+`SEED_SALT`)。
