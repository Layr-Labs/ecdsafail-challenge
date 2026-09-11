# 15 — FW52 生产实测：真实 λ、期望时间、过滤器盲区与战略转向（2026-09-12 凌晨）

## 生产管道（已全自治，长跑中）
- 4×L20 walk_grind_gpu（/tmp/gpu_grind_fw52.sh，STATE=pp_state_fw52.bin，100B/200B/300B/400B 起各400片×10M）
- verify_watch（已修 xargs -P16 -n1，否则默认打包多行=串行！）16路 filter_calib；winner_watch 自动 build+官方eval 写 fw52_WINNER_READY.txt
- 已停 CPU walk_grind（64线程吃满CPU只贡献4%扫描、且低端nonce代表性差）；filter_calib 单线程，16路仅占16核
- 关键运维：setsid 启动须在同一 SSH 会话 sleep>=10s 确认存活再断，否则 watch 会被 SIGHUP 带走

## 实测 λ（推翻文档13的乐观估计）
- λ_walk：第一片4卡扫40M出21 -> P(walk)=5.25e-7 -> λ_walk=14.46（文档13估13.2，偏乐观3.5×）
- λ_rest：22个高端GPU walk-clean候选，mean classical=7.05、mean phase=6.14、sum=13.18
- c-p 强正相关 corr=0.741（c小则p小，独立Poisson偏悲观，但只够补偿数倍）
- 独立估 P(0/0|walk)=e^-13.18=1.88e-6；总P=9.87e-13；19,047/s -> 期望~616天/个
  计入强相关现实期望=数十天级。结论：4×L20 上 island-exact 微调是月级，非数日，不可作短期冲榜手段
- 对照基线base：λ_walk13.3、λ_rest10.6，比FW52好搜~50×；压缩fold把λ_rest从10.6抬到13.18，省0.015%分却难搜~13×，极不划算

## 决定性根因=过滤器盲区（唯一数量级破局方向）
- walk_grind.rs L3-12 自述：只建模 fold-window walk(classical)；chunk/flag compare 是 phase-only
  修复，过滤器"cannot see phase-garbage" -> 残余 p=6 全来自此，c=7 部分来自 compare classical
- 整条电路是 classical-control + quantum-data，compare 相位踢本可纯经典 U256 仿真
- 破局：在 walk_grind(932行,U256/EC/Val/fold_apply 基建齐全)里补 chunk/flag compare 相位判据，
  GPU粗筛直接滤掉 phase 脏 nonce。λ_rest 13.18->若~3 则期望 616天->0.4天。宁松勿漏(漏判丢真winner)
- 这是研究级CUDA/Rust开发，是接下来主攻方向，而非继续拧 PP_REPLAY_* 参数

## 战略
1. 立即提交基线 1,137,423,406（现成nonce 2886213855485 0/0/0=榜首水平,零风险占名）—待用户确认
2. FW52/c4 后台长跑当零成本彩票（winner_watch自动到待提交）
3. 主攻强化过滤器(compare phase)，这是把月级拉回天级的唯一现实路径
4. CAP7 value-exact 已正确实现(u64->u128)但只多删4 Toffoli(0.0004%)，已回退CAP6，勿再试

## 增量印证（35候选, 01:39）
mean_c=7.71/mean_p=6.94；出现首个 classical=0 候选，但 phase=0 个数仍为0，min c+p=3。
=> phase 比 classical 更顽固、且恰是 walk 过滤器不看的维度，memory16 的 compare-phase 强化是最高收益方向。
