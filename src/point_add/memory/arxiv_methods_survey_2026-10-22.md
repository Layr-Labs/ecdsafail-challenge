# ECDSA.Fail 相关论文与线路优化方法综述

更新日期：2026-10-22  
研究对象：`Layr-Labs/ecdsafail-challenge` 中的 secp256k1 可逆点加线路  
资料范围：以 arXiv 原文为主，少量没有 arXiv 版本但被核心论文直接依赖的 IACR ePrint 单独标注。

## 0. 先给结论

这项挑战优化的不是完整 Shor 算法，而是其中反复调用的一个内核：

\[
|R\rangle\longmapsto |R+A\rangle,
\]

其中 $R=(x_R,y_R)$ 是量子寄存器中的椭圆曲线点，挑战默认把 $A=(x_A,y_A)$ 当成经典常量。对仿射坐标，核心计算是

\[
\lambda=(y_R-y_A)(x_R-x_A)^{-1},\qquad
x_{R'}=\lambda^2-x_R-x_A,\qquad
y_{R'}=\lambda(x_A-x_{R'})-y_A.
\]

真正占成本的是模逆以及围绕模逆的可逆清理。现有方法可以浓缩成一句话：

> 不再把完整扩展 Euclid 历史一直保存在量子内存中，而是只保存一份尽可能短的“决策录音带”，随后用它重放模除/模乘；同时把空闲线路借给加法器，把 secp256k1 的特殊模数写进每一层算术，并通过测量辅助清理减少非 Clifford 工作。

当前至少有三条不同的资源路线：

| 路线 | 主要目标 | 模逆架构 | 典型特点 |
|---|---:|---|---|
| 极低宽度 | 最少逻辑比特 | register-shared EEA / shrunken-PZ | 约 825–835 比特，但 Toffoli 很多 |
| 论文截止时的乘积最优 | 降低 $Q\times T$ | Jump-2 dialog-GCD + base-5 transcript | 约 1151 比特、约 1.30M 平均 Toffoli |
| 截止后低门数路线 | 更低 Toffoli | ping-pong，后续发展成 leapfrog | 用较长一比特 transcript 换掉全宽比较/交换 |

当前本地提交 `3eefcf21` 已发展为 leapfrog 线路：1234 个峰值逻辑比特、755,313.657 个平均执行 Toffoli，乘积约 $9.32057\times10^8$，并通过当前 9,024 个 Fiat–Shamir 验证样本。这个数字是挑战分数，不是完整 Shor 成本，也不是全输入正确性的证明。

## 1. 从完整 Shor 到挑战内核

完整 ECDLP Shor 计算大致是：

1. 准备指数寄存器 $u,v$ 的叠加；
2. 可逆地计算 $[u]G+[v]P$；
3. 对指数寄存器做 Fourier 变换；
4. 测量和经典后处理，恢复离散对数。

第 2 步由大量受控点加组成。窗口化后，不再逐比特执行约 512 次点加，而是每次读取一个 $w$-bit 窗口，从 QROM 中选择预计算点再做点加。以 $n=256,w=16$ 的常见估算为例，完整调度约需 28 次窗口点加，并为每次查表支付额外成本。

挑战只交付其中一个 `point_add` 调用，而且默认 $A$ 已经是经典已知值。因此，从挑战线路到完整 Shor 还缺：

- 两个标量乘法的完整窗口调度；
- 量子地址控制的 QROM lookup/use/unlookup；
- 无穷远点、相等点、互逆点等 exceptional cases；
- Fourier 层、测量与经典后处理；
- 多次点加复合后的相干误差分析；
- 面向具体纠错码和硬件的路由、深度、magic-state 工厂及解码成本。

挑战仍然重要，因为点加是最大的逻辑内核，而仿射点加中的模逆通常占一次点加约 90% 的非 Clifford 算术成本。

## 2. 论文地图

### 2.1 直接决定当前挑战架构的论文

| 年份 | 论文 | 关键贡献 | 与本仓库的关系 |
|---:|---|---|---|
| 2025 | [Verifiable Quantum Advantage via Optimized DQI Circuits, arXiv:2510.10967](https://arxiv.org/abs/2510.10967) | 隐式 Bézout 系数、record/replay EEA、原位架构 | dialog-GCD 思想源头；原应用是 Reed–Solomon 解码，不是 ECDLP |
| 2026 | [Securing Elliptic Curve Cryptocurrencies against Quantum Vulnerabilities, arXiv:2603.28846](https://arxiv.org/abs/2603.28846) | 给出 Google 的低宽度/低门数上界并用零知识证明证明存在性 | 发起公开追赶的直接背景；未公开线路细节 |
| 2026 | [Optimized Point Addition Circuits for Elliptic Curve Discrete Logarithms, arXiv:2606.02235](https://arxiv.org/abs/2606.02235) | 首个公开、详细的 record/replay ECDLP 点加构造；近似算术与 pseudo-Mersenne 特化 | 挑战初期最重要的公开算法模板 |
| 2026 | [Quantum Algorithm for ECDLP with Space-Efficient Point Addition, arXiv:2607.13816](https://arxiv.org/abs/2607.13816) | register-shared EEA、长度寄存器、位置控制算术；256-bit 为 835 qubits | 低比特分支的理论来源 |
| 2026 | [ECDSA.Fail: Open Autoresearch for Optimizing Elliptic-Curve Point Addition in Shor’s Algorithm, arXiv:2609.09582](https://arxiv.org/abs/2609.09582) | 挑战定义、截至 7 月的 Pareto frontier、Jump-2/base-5、ping-pong、Karatsuba square、低宽度路线 | 挑战主论文 |
| 2026 | [Efficient Record-and-Replay Arithmetic for Quantum Elliptic-Curve Point Addition, arXiv:2609.28882](https://arxiv.org/abs/2609.28882) | 对 Jump-2、ping-pong、fused replay、窗口接口和正确性反例做专门分析 | 当前最贴近代码的算术论文；明确指出仍存在 supported-input counterexamples |

### 2.2 ECDLP 线路与资源估算的主干

| 年份 | 论文 | 主要方法/地位 |
|---:|---|---|
| 2003 | [Proos–Zalka, Shor's discrete logarithm quantum algorithm for elliptic curves, quant-ph/0301141](https://arxiv.org/abs/quant-ph/0301141) | 首批具体 ECDLP Shor 构造；指出 Euclid 模逆和输入相关停止时间是主要难点；提出共享 shrinking remainder 与 growing coefficient 空间的思想 |
| 2017 | [Roetteler et al., Quantum resource estimates for computing elliptic curve discrete logarithms, arXiv:1706.06752](https://arxiv.org/abs/1706.06752) | 完整模拟受控点加 Toffoli 网络；给出 $9n+2\lceil\log_2n\rceil+10$ qubit 级别的旧基线 |
| 2020 | [Häner et al., Improved quantum circuits for elliptic curve discrete logarithms, arXiv:2001.09580](https://arxiv.org/abs/2001.09580) | 改写 binary EEA、窗口算术、移动 uncompute 时机，并提供 Q# 实现 |
| 2023 | [Litinski, How to compute a 256-bit elliptic curve private key with only 50 million Toffoli gates, arXiv:2306.08585](https://arxiv.org/abs/2306.08585) | 从完整算法和 active-volume 架构估算 256-bit ECDLP；讨论并行摊销模除和复用状态 |
| 2026 | [Häner et al., Computing 256-bit elliptic curve discrete logarithms in 26 days..., arXiv:2609.05625](https://arxiv.org/abs/2609.05625) | 把 Schrottenloher 逻辑线路编译到 trapped-ion 架构；约 1450 logical qubits、40M Toffoli，估算 19,397 physical qubits、25.7 天 |

另有两篇相关但不直接决定本挑战 prime-field 内核的工作：

- [Quantum resource estimates for computing binary elliptic curve discrete logarithms, arXiv:2503.02984](https://arxiv.org/abs/2503.02984)：研究二元域曲线，算术结构不同；
- [Performance analysis of a repetition cat code architecture..., arXiv:2302.06639](https://arxiv.org/abs/2302.06639)：物理层 cat-code 资源估算。

### 2.3 可逆算术、空间复用与编译基础

| 论文 | 方法 | 在挑战中的作用 |
|---|---|---|
| [Cuccaro et al., A new quantum ripple-carry addition circuit, quant-ph/0410184](https://arxiv.org/abs/quant-ph/0410184) | 常数辅助位的 ripple-carry adder | 大量加/减法的基础结构 |
| [Gidney, Halving the cost of quantum addition, arXiv:1709.06648](https://arxiv.org/abs/1709.06648) | temporary logical-AND；计算 AND 付费，测量辅助清理近乎不再付 T | `Hmr`/测量式进位清理的思想基础 |
| [Parent–Roetteler–Mosca, Karatsuba-based integer multiplication, arXiv:1706.03419](https://arxiv.org/abs/1706.03419) | 可逆 Karatsuba 与 pebbling 的时空权衡 | `square.rs` 的递归乘法/平方基础 |
| [Gidney, Windowed quantum arithmetic, arXiv:1905.07682](https://arxiv.org/abs/1905.07682) | 小型 table lookup 使控制位成组处理 | 从挑战的经典 addend 接口扩展到完整 Shor 的 QROM/window 接口 |
| [Kornerup–Sadun–Soloveichik, Tight bounds on the spooky pebble game, arXiv:2110.08973](https://arxiv.org/abs/2110.08973) | 用测量回收量子空间的理论时空界 | 解释为什么“测掉垃圾、稍后修相位”能换取更低峰值宽度 |
| [Quist–Laarman, Trade-offs between classical and quantum space using spooky pebbling, arXiv:2401.10579](https://arxiv.org/abs/2401.10579) | 经典/量子空间的 pebbling 权衡 | 对 recompute、live-range splitting 提供一般框架 |
| [Luongo et al., Measurement-based uncomputation of quantum circuits for modular arithmetic, arXiv:2407.20167](https://arxiv.org/abs/2407.20167) | 系统化 MBU，并用于各种模加/比较 | `cond_pass` 和 phase-correction 类优化的理论背景 |
| [Khattar–Gidney, Rise of conditionally clean ancillae..., arXiv:2407.17966](https://arxiv.org/abs/2407.17966) | 条件干净 ancilla、laddered toggle detection | 从已有系统寄存器借线，降低局部加法器 workspace |
| [Gidney, A Classical-Quantum Adder with Constant Workspace and Linear Gates, arXiv:2507.23079](https://arxiv.org/abs/2507.23079) | 3 clean ancilla + $4n+O(1)$ Toffoli，或 2 clean + $n-2$ dirty ancilla + $3n+O(1)$ | 固定模数校正、vented/dirty adder 路线 |
| [Ruiz et al., Quantum circuit optimization with AlphaTensor, arXiv:2402.14396](https://arxiv.org/abs/2402.14396) | 通过张量/程序搜索寻找局部线路恒等式 | 适合未来自动综合小型 kernel，不直接产生当前主架构 |

没有合适 arXiv 版本、但 ping-pong/leapfrog 理论上直接相关的两项是：

- Bigou–Tisserand, *Improving modular inversion in RNS using the plus-minus method*, [IACR ePrint 2015/193](https://eprint.iacr.org/2015/193)；
- Bernstein–Yang, *Fast constant-time GCD computation and modular inversion*, [IACR ePrint 2019/266](https://eprint.iacr.org/2019/266)。

## 3. 方法总整理

### 3.1 点加层：把一个非原位公式改成原位可逆流程

朴素公式会同时需要输入点、输出点、斜率和若干临时寄存器。Proos–Zalka 观察到，斜率既可以从输入恢复，也可以从输出恢复：

\[
\lambda=\frac{y_R-y_A}{x_R-x_A}
=-\frac{y_{R'}+y_A}{x_{R'}-x_A}.
\]

因此两条 256-bit 坐标寄存器可以被原位覆盖。挑战主线路采用的高层序列是：

1. $X\leftarrow x_R-x_A,\;Y\leftarrow y_R-y_A$；
2. $Y\leftarrow YX^{-1}=\lambda$；
3. $X\leftarrow X+3x_A$；
4. $X\leftarrow X-Y^2=x_A-x_{R'}$；
5. $Y\leftarrow YX=\lambda(x_A-x_{R'})$；
6. $Y\leftarrow Y-y_A=y_{R'}$；
7. $X\leftarrow x_A-X=x_{R'}$。

优化意义：这套数据流决定了两个模逆/模乘高峰、平方高峰，以及哪些 addend 数据能够在低峰时临时物化。

正确性边界：普通混合点加默认排除 $R\in\{A,-A,-2A\}$ 等特殊情形；完整 Shor 必须另外处理或证明不会进入这些分支。

### 3.2 模逆路线 A：传统 reversible binary EEA / Kaliski

做法：把 binary extended GCD 展开成固定长度的可逆状态机，同时保留足够历史，以便把所有分支和临时值 uncompute。

优点：结构直观，已有较成熟的精确线路；缺点：历史栈、商位、比较结果、交换控制和 Bézout 系数同时存活，宽度很大。

挑战早期的主变化不是更换算法，而是：

- packing：把不会同时使用的字段塞入相同物理寄存器；
- recomputation：删掉长寿命缓存，需要时重算；
- live-range reduction：更早 uncompute/release；
- 动态位宽：余数变小时归还高位线路。

主论文将这一阶段概括为从 2715 qubits 压到约 2002 qubits。

### 3.3 模逆路线 B：register-shared EEA / shrunken-PZ

关键不变量是：Euclid 余数不断变短，而 Bézout 系数不断变长，二者的长度和不会同时达到最大。因此可让它们共享两个物理 bank，并移动所有权边界。

Luo 等人的构造进一步使用：

- 两个共享 work register；
- remainder、cross-cofactor 和 quotient 的嵌入式存储；
- length register；
- rotation/location cursor；
- 仅对当前有效窗口做位置控制加减；
- 中途测量和 classical feed-forward 来清理局部垃圾。

理论资源为：

- 模逆：$2n+6\lfloor\log_2n\rfloor+O(1)$ qubits；
- 完整仿射点加：$3n+6\lfloor\log_2n\rfloor+O(1)$ qubits；
- $n=256$ 时论文给出 835 logical qubits。

挑战低宽度分支进一步用 lane lending、metadata narrowing、lifetime splitting 把样本验证宽度做到 825 qubits，但 T 成本约 489M。它证明“极低宽度可行”，但不是当前 $Q\times T$ 最优。

### 3.4 模逆路线 C：dialog-GCD record-and-replay

这是高分路线的核心。

### Record

正向只运行两个会缩短的 GCD operand，不再同步维护完整 Bézout 系数。每一步只保存做了什么：奇偶、减法、交换、移位等决策，形成量子 transcript $\tau$。

### Replay

GCD 结束后，把 $\tau$ 反向重放到 payload/coefficient 寄存器。由于每个 GCD 步骤对模 $p$ 的系数是线性变换，同一 transcript 可以完成

\[
D_x(0,y)=(yx^{-1},0),\qquad D_x^{-1}(y,0)=(0,yx).
\]

所以同一架构既做点加第 2 步的除法，也做第 5 步的乘法。

主要收益：把“长时间存活的 Bézout 系数和历史”换成“压缩 transcript + 可缩短的 operand”。主要代价：transcript 本身仍然是量子数据，不能直接测量或丢弃；replay 需要大量受控模算术。

### 3.5 Jump-2：一次处理一到两个除二步骤

普通 dialog-GCD 每个边界做一次 parity/compare/swap/subtract/halve。Jump-2 把相邻 divstep 合并成 macro-step：在正常边界先无条件除二，再根据下一次奇偶决定是否额外除二，然后完成减法和交换。

效果：

- 减少 macro-step 数；
- 减少全宽比较、交换、减法块和 transcript 边界；
- 条件于在固定预算内收敛时，它与普通 dialog-GCD 的算术变换相同。

问题：可逆线路不能按输入相关时间停止，所以仍需固定轮数。主论文报告从 258 增至 261 macro-steps 后，千万输入上的不收敛率从 $2.839\times10^{-4}$ 降到 $2.86\times10^{-5}$，仍不是全输入终止证明。

### 3.6 Base-5 transcript codec

Jump-2 的一个 raw symbol 是三个布尔量，看似需要 3 qubits，但八种组合中只有五种可达。因此把每个 symbol 映射为 base-5 digit：

\[
z=d_0+5d_1+25d_2<125<2^7.
\]

三枚 raw symbol 原需 9 qubits，现在只需 7 qubits。261-step 配置从 783 个 raw transcript qubits 压到 609 个，节省 174 qubits。

这不是有损压缩：编码器要在完整 Hilbert 空间上扩展成置换，decode 后还原全部 symbol，并把释放的两条线相干地归零。

进一步优化是 streamed codec/replay：

- operand 高位随着 GCD 缩短而释放；
- 已完成的 symbol group 立即编码进这些空位；
- replay 时一次 decode 一组、消费并归零；
- 避免“完整 operand + 完整 transcript + 完整 payload”同时达到峰值。

### 3.7 Ping-pong：去掉 GCD value walk 的全宽比较与数据相关交换

把两个 operand 都保持为奇数，并固定交替更新目标寄存器。对 source $s$、target $t$，只看二者第二低位：

\[
e=t[1]\oplus s[1],\qquad
t'=(t+(-1)^e s)/2.
\]

若它们模 4 同余就取和，否则取差，结果除二后仍为奇数。每轮只记录一个 sign bit，不需要：

- 比较 $|s|$ 和 $|t|$；
- 根据比较结果交换两个 256-bit 寄存器；
- 保存多比特 Jump-2 symbol 并执行 codec。

其权衡是：

- transcript 更长：论文实现固定 704 个 one-bit rounds；
- 局部 symbol 很便宜；
- 宽度比 Jump-2 大一些，但执行 Toffoli 显著更少。

论文中的原始 post-cutoff 点为 1321 qubits、952,707 average Toffoli，$Q\times T\approx1.259$B。

重要限制：论文发现 99,998 个非恒等输入中有 33 个需要超过 704 轮，另有 8 个违反 shrink-width schedule；因此“理想 recurrence 最终收敛”不等于“当前有限轮数实现对全部输入正确”。

### 3.8 Leapfrog：当前仓库的下一代 ping-pong（尚无独立 arXiv 定稿）

当前 `leapfrog.rs` 每 tick 不只做一次 plus/minus-halving，而是：

1. 连做三次由低位决定符号的固定 ping-pong step；
2. 第四次在 deep/flat 候选间选择；
3. 计算额外 trailing zeros $e\in[0,3]$；
4. 用两级 barrel 一次去掉 $2^e$；
5. payload 端做对应的四次 add/halve 和受控 $2^{-e}$；
6. 两条 rail 仍按固定节奏交替，不做 data-dependent route。

可理解为：把多次 one-bit ping-pong 合并成一枚更强的 leap，同时保留 transcript/replay 的线性结构。源码中的后续优化包括：

- 每 tick 的 width schedule；
- payload 操作和 rail 操作交错；
- 一折/三折 fused cells；
- rail top wire loan；
- 固定 cap 下逐 tick 重新选 chunk plan；
- 分阶段的 compare/fold window；
- 针对具体 op stream 的精确 post-pass。

这条路线的最新数字来自本地验证记录，不来自上述 9 月论文。应把它称为“当前挑战实现前沿”，而不是已经完成同行评议的全输入线路。

### 3.9 Fused replay cell

逆向 replay 的基本更新是

\[
z\leftarrow 2z\pm y\pmod p.
\]

朴素实现先 double + modular correction，再 signed add + 第二次 correction。fused replay 保留 doubling overflow 和 addition carry/borrow，合并成一次修正：

\[
2z\pm y=w+\kappa2^{256}\equiv w+\kappa F\pmod p,
\quad F=2^{32}+977.
\]

在论文的同等 56-bit fold 配置中，单个 inverse cell 从 446 降为 393 static Toffoli，约降 11.9%，workspace 从 87 增到 88 qubits。

注意：全宽代数是精确的；当前实现只在 56-bit correction window 中做 fold，遗漏窗口外 carry/borrow 会成为近似误差。

### 3.10 secp256k1 pseudo-Mersenne 特化

secp256k1 prime 为

\[
p=2^{256}-F,\qquad F=2^{32}+977.
\]

于是每次溢出 $2^{256}$ 不需要一般模除，只需在低位加一个很短的 $F$。而

\[
F=2^{32}+2^{10}-2^5-2^4+1
\]

还可写成稀疏 signed-binary/NAF 形式，用移位和少数加减替代一般常数乘法。仓库中的 fold width、compare width、chunk shape，本质都在优化这些短修正。

风险：截短 correction window、截短 carry recovery 或把概率很小的高位假设成零，都可能让值看起来正确但留下 phase garbage。

### 3.11 Karatsuba modular square-subtract

点加需要 $X\leftarrow X-\lambda^2\pmod p$。令

\[
\lambda=L+2^{128}H,
\]

并计算

\[
A=L^2,\quad B=H^2,\quad C=(L+H)^2.
\]

则

\[
\lambda^2=A+2^{128}(C-A-B)+2^{256}B
\equiv A+2^{128}(C-A-B)+FB\pmod p.
\]

当前做法的几个叠加优化：

- square-specific Karatsuba，而不是通用乘法；
- 利用平方对称性，只算一次 $z_i z_j$；
- 直接把 $A,B,C$ 的贡献累加到目标 $X$，不物化完整 512-bit product；
- build–apply–unbuild，使 $A,B,C$ 不同时存活；
- product bits 和 carries 用完立刻清理或外借；
- $2^{256}\equiv F$ 直接做 sparse low-word correction。

论文统计半尺寸三平方的 off-diagonal products 为 24,512，较直接 256-bit 对称平方的 32,640 少约 24.9%。Karatsuba 恒等式本身精确；近似只来自其下层有限宽度校正。

### 3.12 加法器、carry venting 与 ancilla 借用

### Ripple-carry

Cuccaro/Gidney ripple adder 用线性 Toffoli 成本传播 carry，适合本项目大量不同位宽的 add/sub。

### Temporary logical-AND / measurement uncompute

先付非 Clifford 成本计算 carry/product AND，使用后把 ancilla 在 X basis 测量，并用 Clifford 相位修正清理。它省掉反向 Toffoli，但要求 phase correction 完整。

### Dirty/conditionally-clean ancilla

当某些系统位在当前控制分支上已知为零，或其值在一段时间内不会被读取时，可把它当 carry workspace 使用，最后恢复。这对应仓库中的：

- source/result top loan；
- rail top loan；
- sign loan；
- retained zero/product/cross-term loan；
- terminal-state rail loan；
- square assembly loan。

### Vented classical-quantum adder

Gidney 2025 的构造给出 3 clean ancilla、约 $4n$ Toffoli 的常数加法，或利用 $n-2$ dirty ancilla 把成本降到约 $3n$。这对“加固定模数 $p$ 或固定 correction $F$”尤其合适。

### 3.13 Width schedule、chunking 与 interleaving

降低峰值不是简单删 qubit，而是让同一批 qubit 在不同时间扮演不同角色。

### Shrinking widths

GCD operand 的绝对值逐步缩小，于是高位可以按 round 释放。若 schedule 有严格上界，这是精确优化；若仅由样本最大值拟合，则是近似优化。

### Chunked add

完整 ripple 的 carries 放不下时，把加法切成多个 chunk；chunk boundary carry 可以测量释放，再用局部比较恢复相位。chunk 越短，workspace 越小，但多出边界修复 Toffoli，并增加截断比较风险。

### Head / middle / tail replay

`pingpong.rs` 把 replay 分成三段：

- head：walk 已释放部分空间后批量 replay；
- middle：每轮 walk 旁边立即 replay；
- tail：GCD 到 signed-unit endpoint 后，两条大 operand rail 几乎全部释放，再批量 replay。

这种 interleaving 避免 transcript、full walk state 和 payload 在同一时刻同时达到最大。

### Plateau 与 co-binders

宽度由同一峰值上的多个 site 共同决定。只优化一个 site，峰值往往不动；必须同时消掉所有 co-binders。源码中 cap、per-tick table、phase cap、bridge budget、square replan 都是在处理这个问题。

### 3.14 常量传播与经典 addend 特化

挑战 addend $A$ 是经典常量，因此所有由 $x_A,y_A$ 控制的块都可在编译/执行时常量传播：控制位为 0 的块完全不执行。这对 challenge 的 average executed Toffoli 很有利。

但完整窗口 Shor 中，$A$ 是由量子地址选择的 QROM 输出，不能直接把每个 table bit 当经典分支。需要：

1. lookup 量子选中的坐标；
2. 使用通用、相干的 addend arithmetic；
3. unlookup 并清除 phase/ancilla。

因此经典 addend 分数必须另算 window-compatible overhead。论文中的 $w=16$ Jump-2 windowed kernel 为 1162 qubits、约 1.523M work；ping-pong windowed kernel 为 1338 qubits、约 1.128M work。它们仍只是一次 window-selected point addition。

### 3.15 精确编译后处理

当前仓库已经不只是“手写量子算法”，还包含面向固定 op stream 的布尔/代数优化器：

- affine simplification：跟踪 GF(2) 仿射表达式；
- quadratic simplification：识别二次布尔关系；
- truth-table simplification：小 support 上精确枚举；
- product witness：识别某控制已蕴含另一个控制，令 CCX 降成 CX 或删除；
- dead-code/cancel：自逆门对消、无影响的控制块删除；
- constant propagation：经典输入触发的 gate pruning；
- source-bound edit tables：对已验证固定 stream 的特定位点做精确重写。

这些优化通常只省一个或几个 Toffoli，但在前沿上仍有价值。当前 score 对一个无条件 Toffoli 的边际价格就是峰值 $Q$，约 1234 分。

需要区分两类“精确”：

- 对完整输入空间精确的布尔恒等式；
- 只对当前固定 operation stream 和声明 support 精确的重写。

即使重写本身精确，只要 gate stream 改变，Fiat–Shamir 输入集合也会改变，原来依赖幸运 nonce 的近似线路可能立刻在新样本上失败。

### 3.16 Nonce hunting 与 support selection

验证输入由提交 operation stream 的 hash 派生。保持语义线路不变、只改变尾部 identity nonce，可以换一组测试输入。因此：

- nonce search 不降低真实 gate cost；
- 它只是在有限输入空间里寻找不触发已知近似错误的“岛”；
- 9,024/9,024 pass 证明的是该提交 hash 对应样本上的 value/phase/ancilla clean；
- 它不证明完整输入域正确，更不证明叠加态上的完整 Shor 相干正确。

主论文明确把这类分数称为 finite-support benchmark，而不是经过认证的 fault-tolerant resource estimate。

## 4. 方法与当前源码的对应关系

| 源码 | 主要概念 | 论文来源/状态 |
|---|---|---|
| `src/point_add/mod.rs` | 原位点加数据流、固定 recipe、post-pass、tail nonce | Proos–Zalka + 挑战主论文；当前参数晚于论文 |
| `src/point_add/pingpong.rs` | fixed-alternation GCD、one-bit tape、head/mid/tail replay、width schedule、chunk add | arXiv:2609.09582 / 2609.28882 |
| `src/point_add/leapfrog.rs` | 四个 plus/minus-half step、deep/flat、trailing-zero barrel、rail/payload interleaving | ping-pong 的后续实现前沿；尚无独立 arXiv 论文 |
| `src/point_add/square.rs` | symmetric Karatsuba square、直接累加、assembly/carry loans | arXiv:1706.03419 + 2609.09582 |
| `src/point_add/modular.rs` | ripple/chunk add、pseudo-Mersenne fold、source/result loans | Cuccaro、Gidney、Schrottenloher、挑战改进 |
| `src/point_add/cond_pass.rs` | 测量辅助清理、条件相位修复、reset/measurement 后处理 | arXiv:1709.06648 / 2407.20167 |
| `affine_simplify.rs` | 仿射 support 精确化简 | 编译器式本地方法 |
| `quadratic_simplify.rs` | 二次布尔 support 精确化简 | 编译器式本地方法 |
| `truth_simplify.rs` | 小 support truth-table、product witness | 与 AlphaTensor/局部 superoptimization 同类，但为项目专用实现 |
| `stream_edits.rs`, `source_edits.rs`, `*_base.rs` | 固定流上的索引化重写、已验证生成表 | 挑战工程方法；不是通用论文算法 |
| `width_composition.rs`, `compact_*` | 给定当前可用 room 自动选择 chunk plan | 空间受限可逆加法的调度层 |
| `top_result_loan.rs`, `y33_clears.rs`, `y42_bound_pass.rs` | 高位/rail 生命周期借用与归还 | conditionally-clean ancilla + 源码特化 |

## 5. 各路线资源与证据不能混为一个排行榜

| 构造 | $Q$ | work / $T$ | 正确性证据 | 备注 |
|---|---:|---:|---|---|
| Google low-Q bound | ≤1175 | ≤2.7M | ZK-attested 0/9024 FS | 线路未公开 |
| Google low-gate bound | ≤1425 | ≤2.1M | ZK-attested 0/9024 FS | 是上界，不是公开实际值 |
| Schrottenloher low-Q + $w=16$ | 1208 | ≈2.59M | 10,000 random + block-level simulation | 公开详细构造 |
| Luo et al. full ECDLP logical width | 835 | 渐近 $1056n^3/\log n+O(n^2)$ | 理论构造 + 数值实验 | 目标是完整算法宽度，不同计数口径 |
| ECDSA.Fail July best $Q\times T$ | 1151 | 1.299M | 0/9024 FS；独立 100k 有约 0.192% any-channel error | classical addend |
| Windowed Jump-2 | 1162 | 1.523M | 215/100k fresh failures | single-call $w=16$ |
| Windowed ping-pong | 1338 | 1.128M | 39/100k fresh failures | single-call $w=16$ |
| Conservative ping-pong | 1392 | 1.253M | 0/100k fresh；仍有构造化反例 | 不是 all-input proof |
| Targeted repaired ping-pong | 1419 | 1.356M | 0/100k new；仍有 schedule counterexamples | 论文修复版 |
| 当前本地 leapfrog `3eefcf21` | 1234 | 0.755314M | 0/9024 current FS | 更晚的挑战前沿；classical addend；无全输入证明 |

这里的 work 口径并不完全统一：有的数 CCX+CCZ，有的把 AND 也算入；有的是 average executed，有的是 construction/static；有的已经含 $w=16$ lookup allowance，有的没有。不能只按一个数字宣称正式超越。

## 6. 正确性需要分五层看

### 6.1 值正确

对 computational-basis 输入，输出坐标是否等于经典椭圆曲线点加结果。

### 6.2 ancilla clean

所有临时量子位是否真的回到 $|0\rangle$。只看输出坐标发现不了残余垃圾。

### 6.3 phase clean

测量式 uncompute 是否给每个分支补上正确相位。值可以完全正确，但残余相位会破坏 Shor 的干涉。

### 6.4 单次调用相干正确

对任意叠加态，整个 point-add channel 是否等于理想 unitary/isometry，而不只是逐 basis state 看起来正确。测量 outcome 的概率也不能泄露输入信息。

### 6.5 完整算法复合正确

在 28 次左右窗口点加以及相关中间态分布上，坏子空间权重怎样累积。独立随机点的错误率不能直接当作完整 Shor 的每步独立错误率。

`arXiv:2609.28882` 给出的具体警告包括：

- zero payload 可能出现非 canonical word $p$，导致 duplicate/XOR cleanup 失败；
- chunk carry cleanup 若遗漏 equality term，会留下输入相关 phase；
- 56-bit correction window 之外的 carry 会造成 replay 错误；
- 704-round schedule 和 shrink-width schedule 有显式反例；
- zero-slope 点可以输出正确坐标却触发 phase flags。

因此目前最诚实的表述是：

> 算法恒等式（record/replay、ping-pong、Karatsuba）大多有清楚的条件性证明；最高分实现包含有限轮数、有限位宽和有限 support 的近似工程选择，当前公开验证不足以推出 all-input coherent correctness。

## 7. 大家实际上怎样优化排行榜

一次有效优化通常沿以下闭环发生：

1. **找高峰而不是看总代码**：记录哪个 round/site 把 active qubits 顶到 $Q$。
2. **确认 co-binders**：同一高度可能有几十个峰；只降一个没有分数收益。
3. **给 qubit 定价**：若降低 1 qubit 会增加 $\Delta T$，只有当
   \[
   (Q-1)(T+\Delta T)<QT
   \]
   才值得。在当前 $Q=1234,T\approx755{,}314$ 下，一枚 qubit 的 break-even 约为 $T/(Q-1)\approx612.6$ 个平均 Toffoli。
4. **先做结构优化**：换 GCD recurrence、fusion、interleaving、loan、direct accumulation。
5. **再做局部计划**：逐 tick 决定 chunk width、compare width、fold width、carry hosting。
6. **跑三通道检查**：classical value、phase garbage、ancilla garbage。
7. **对近似改动测失败密度**：独立 corpus、构造化反例、边界输入，而不只看 9024 FS。
8. **最后才 grind nonce**：nonce 只能寻找 support 岛，不能修复算法。
9. **固定 stream 后跑 post-pass**：affine/quadratic/truth/product simplification 和 source-bound edits。

前沿不是靠“一招省 30%”一直推进。大的架构跳跃之后，大量贡献来自：某个 tick 借一条 rail top、某个 chunk 少一枚 carry、某个测量条件下 CCX 变 CX、某个平方子树提前归还一条线。

## 8. 对下一步研究的判断

### 优先级 A：修复正确性但保持低成本

最有价值的问题不是再凭样本缩一位 compare，而是把以下误差源逐个变成有证明的 exact primitive：

- canonical zero representation；
- equality-aware carry cleanup；
- full-width 或有解析上界的 pseudo-Mersenne correction；
- 有证明的 round budget 和 width envelope；
- exceptional point 的相干处理。

### 优先级 B：把 leapfrog 写成论文级对象

需要独立给出：

- 每 tick 变换矩阵；
- oddness/GCD preservation；
- deep/flat 与 trailing-zero 选择的可逆性；
- transcript 到 payload replay 的线性证明；
- 终止上界；
- shrink-width 上界；
- 相位清理不变量。

当前源码注释已经包含很多局部证据，但仍缺一个从 ideal recurrence 到 emitted circuit 的完整证明链。

### 优先级 C：完整 windowed Shor 集成

把当前 classical-addend 内核接入量子地址 QROM，测量真实 lookup/use/unlookup 成本，并检查 28-call correlated state，而不是只测随机单点。

### 优先级 D：自动化局部综合

适合 AlphaTensor/枚举/superoptimization 的对象不是整个 1100 万 op 线路，而是：

- 3–12 bit carry/phase repair kernel；
- base-5 encode/decode 小块；
- sparse-$F$ correction；
- fixed-support CCX/CX/phase identity；
- leapfrog barrel 和 terminal cells。

### 优先级 E：物理成本再排序

挑战只优化 $Q\times\text{average Toffoli}$。完整硬件上还要考虑：

- Toffoli/CCZ depth 和并行度；
- mid-circuit measurement latency；
- classical feed-forward；
- magic-state factory 数目；
- 长距离路由和 memory traffic；
- 纠错码 cycle、物理错误率和 decoder 吞吐。

因此，一个 $Q\times T$ 更低但 measurement depth 更高的线路，未必在 trapped-ion、superconducting、photonic 或 neutral-atom 架构上都更快。

## 9. 推荐阅读顺序

若目的是理解并继续优化本仓库，建议顺序是：

1. [ECDSA.Fail 主论文 2609.09582](https://arxiv.org/abs/2609.09582)：先建立问题、分数和方法全图；
2. [Record-and-Replay 专文 2609.28882](https://arxiv.org/abs/2609.28882)：看 ping-pong、fusion 和具体正确性反例；
3. [Schrottenloher 2606.02235](https://arxiv.org/abs/2606.02235)：看公开的 point-add 与 dialog-GCD 架构；
4. [Khattar et al. 2510.10967](https://arxiv.org/abs/2510.10967)：看隐式 Bézout/dialog 的原始抽象；
5. [Luo et al. 2607.13816](https://arxiv.org/abs/2607.13816)：看极低宽度 register-shared EEA；
6. [Häner et al. 2001.09580](https://arxiv.org/abs/2001.09580) 和 [Roetteler et al. 1706.06752](https://arxiv.org/abs/1706.06752)：理解旧基线是怎样搭起来的；
7. Gidney 的 [temporary logical-AND](https://arxiv.org/abs/1709.06648)、[windowing](https://arxiv.org/abs/1905.07682)、[constant-workspace adder](https://arxiv.org/abs/2507.23079)：补足局部算术；
8. [Häner et al. 2609.05625](https://arxiv.org/abs/2609.05625)：最后看逻辑线路落到真实容错架构后，成本如何重新排序。

## 10. 最简方法树

```text
完整 ECDLP Shor
└── 两个 windowed scalar multiplication
    └── 约 28 次 quantum-addressed point addition
        ├── QROM lookup/use/unlookup
        └── 仿射 point-add 内核（本挑战）
            ├── 坐标加减
            ├── modular divide：dy / dx
            │   ├── reversible binary EEA / Kaliski
            │   ├── register-shared EEA（低 Q）
            │   └── dialog record/replay
            │       ├── Jump-2 + base-5 codec
            │       ├── ping-pong
            │       └── leapfrog（当前源码）
            ├── square-subtract
            │   └── symmetric Karatsuba + direct accumulation
            ├── modular multiply
            │   └── reverse replay + fused cell
            └── 全局调度/编译
                ├── pseudo-Mersenne sparse correction
                ├── MBU / phase repair
                ├── chunking / width schedule / interleaving
                ├── dirty & conditionally-clean loans
                ├── affine/quadratic/truth/product simplification
                └── finite-support validation + nonce selection
```

## 11. 一句话评价当前进度

社区已经把“一个公开的 secp256k1 点加内核”从 2715 qubits × 3.96M average Toffoli 推到本地前沿约 1234 × 0.755M，架构进展是真实且很大；但从“挑战分数很低”到“完整、全输入相干正确、可在具体容错量子机上运行的 Shor 攻击”之间，仍然有窗口接口、特殊点、复合相干错误、终止/位宽证明和物理编译这几道实质关卡。
