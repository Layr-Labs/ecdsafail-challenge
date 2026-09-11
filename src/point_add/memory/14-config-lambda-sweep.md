# 14 — 参数×λ×分数 扫描（2026-09-12 凌晨，决定主跑配置）

## 方法（可复现）
- dump_gpu_state 为每配置生成 GPU state（读 PP env，约 50s/个）；walk_grind_gpu 4卡各扫 300万
  测 walk-clean 率 -> λ_walk；对 walk-clean 候选跑 filter_calib 测残余 classical/phase（λ_rest）
- 速率实测 4742 nonce/s/卡；filter_calib 与 eval_circuit 交叉验证一致（候选1002119111 均 c=3 p=9）

## λ_walk 实测（各 300万，start=1e9）
| 配置 | emitted ops | walk-clean | λ_walk | 全GPU出1候选 |
|---|---|---|---|---|
| base fold53/54 chunk21 flag20 | 12267379 | 5 | 13.30 | 32s |
| c1 chunk20 | 12236037(-31342) | 2 | 14.22 | 79s |
| c2 flag19 | 12250746(-16633) | 1 | 14.91 | 158s |
| c4 chunk20+flag19 | 12219401(-47978) | 2 | 14.22 | 79s |
| FW52 fold52/53 | 12250744(-16635) | 文档13.2(≈base) | ~13.3 | 32s |
结论：降 fold window 几乎不抬 λ_walk；降 chunk/flag 抬 0.9-1.6。基线本身 λ_walk 已 13.3（很激进）。

## λ_rest 实测（walk-clean 候选的残余，随机 nonce 是 c18/p12，条件后塌缩）
| 配置 | 候选残余 c | 残余 p | avgT | score(×1259) |
|---|---|---|---|---|
| base | 3-5(均4.0) | 5-9(均6.6) | 903445 | 1137436877≈基线 |
| c1 chunk20 | 3-4(3.5) | 6-9(7.5) | 902142 | 1135797338 |
| c2 flag19 | 3 | 6 | 902748 | 1136559595 |
| c4 c20f19 | 3-5(4.0) | 9-12(10.5) | 901441 | **1134913680(最低)** |
| FW52 | 9-12(仅2样本,低端nonce,不可靠) | 9-11 | 902049 | 1135679187 |
机制：降 chunk/flag -> phase 残余高；降 fold -> classical 残余高。c4 peak qubits 已确认仍 1259。

## 决策
- 主跑 FW52：λ_walk 最低(候选快2.5×)、分数第二低、GPU↔CPU 已验证零分歧、脚本现成
- c4 备选：分数最低(比FW52再低76.5万)但候选慢且 phase 残余高；state=/tmp/st_c4both.bin，随时可切
- 独立 Poisson 估 P(0/0|walk)=e^-(c+p) 偏悲观(文档11: c/p 相关,实测高于独立估计)，需生产积累 ≥30 候选实测
- 生产：4卡 100B/200B/300B/400B 起各400片×10M + CPU grind 低端 + verify_watch 5路 filter_calib
