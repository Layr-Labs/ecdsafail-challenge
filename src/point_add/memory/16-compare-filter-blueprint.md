# 16 — 强化 GPU/CPU 粗筛器覆盖 compare phase（破局实现蓝图）

## 目标
walk_grind 的 walk_converges 只判 walk+fold-escape；补 chunk/flag compare 的 phase 残留判据，
把 walk-clean 候选残余 mean(c+p)=13.18 压到 ~3，P(0/0|候选)从 e^-13 升到 e^-3，期望数十天->数天。
铁律：宁松勿漏。新判据只能把"确定 phase 脏"的判 None，绝不能把可能干净的丢掉；
必须在数千 nonce 上与 filter_calib(ground truth) 交叉验证到零漏判后才上 GPU。

## ground truth 语义（filter_calib.rs 261行 bit-slice 模拟器）
- phase 是逐 shot 累加量：Z/CZ/CCZ/Neg 异或(cond & 量子线)，Hmr/R 异或(量子线 & 随机测量rv & cond)
- cmp_lt_phase_conditioned(arith/compare.rs L437-495, 及 _with_cin L341)：
  * u 先全 X 取反；前缀 carry 链 forward；最高位 CZ(u[last],v[last]),(u[last],cin),(v[last],cin)
  * inverse 逐位 HMR(carry,m)+cz_if(u[i-1],v[i],m)；相位要全抵消
- 截断本质：只在 u/v 的高 compare 位窗口跑(replay_chunk_compare=21/20, flag=22/19)。
  判据(纯算术)：若两数在该高窗口内已分出大小(最高不等位落在窗口内)->截断精确,无phase残留;
  若高窗口内逐位全等、必须看窗口外更低位才能分胜负->该 compare 点 phase 有风险 -> shot 脏

## 电路 compare 落点(pingpong_div.rs, 本地/tmp/gpu_adapt/pingpong_div.rs 3692行)
- L2473 erase 闭包: chunk_add 每边界 hmr(carry) + cmp_lt_phase_conditioned(acc[hi-c..hi],addend[hi-c..hi]), c=replay_chunk_compare
- L2758 / L3097 / L3127: cmp_lt_phase_conditioned(target[N-flag..],source[N-flag..]), flag=replay_flag_compare
- L1472 另一处 cmp_lt_fast_prefix + 高位 CZ(同构)
- replay 主体: replay_halving_round L2003 / replay_doubling_round L2025 / replay_halving L3201 / replay_doubling_inverse L3227

## walk_grind.rs(932行,本地/tmp/gpu_adapt/) 现有可复用基建
- Val(264位扩展 lo:U256+hi) bit/mask_to/add/sub/shr1/ashr1/sext264/is_exact_pm1
- walk_converges L601 双轨(A截断出sign流/B精确收敛到±1)；fold_apply L371/fused_halve_round L527/double_round L556 已是同类截断escape判据(返Err=脏)
- nonce_walk_clean L756 逐shot; eval_batch_walk L716 div用WDIV/mul用WMUL(include! fast_filter_tables.inc)
## 实现步骤
1. 在 walk 双轨 replay 处,对每个 chunk 边界/flag 点取对应 u,v(需对齐 round/tape/bounds 索引)
2. 加 cmp_window_dirty(u,v,window_hi,window_bits)->bool: 高窗口全等且窗口外存在可分胜负的位 => 脏
3. 先在 CPU walk_grind 实现+加开关 env, 对 2000+ nonce 同时跑新判据与 filter_calib,
   列联表核对: 新判据说clean的必须 filter_calib phase=0(允许说脏但实际clean=偏松,不可反向)
4. 零漏判后移植 CUDA(gpu_island2.cu / walk_grind_gpu),重dump state,测速与富集倍数
5. 用富集后真实密度重估期望时间,再定主跑配置
