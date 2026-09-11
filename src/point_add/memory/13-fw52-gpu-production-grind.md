# 13 — FW52 GPU 生产磨启动（2026-09-11）

## 配置
- 目标：FW52（`PP_REPLAY_FOLD_WINDOW=52 PP_REPLAY_FOLD_WINDOW_MUL=53`），avgT≈902,048.6，Q=1259
- P(干净)=1.59e-10（λ_walk≈13.2 + λ_rest≈9.37），期望 6.29e9 nonce 出一个
- 状态文件 `/tmp/pp_state_fw52.bin`（n_ops=12250744，与 filter_calib 输出一致）

## 已验证事实
1. GPU↔CPU 走步判定在真实 FW52 流上零分歧：各扫 0..2.5M，双方唯一命中都是 nonce=2199585
2. nonce=2199585 filter_calib 真值：classical=7 phase=5（走步干净但残余失败，符合 e^-9.37）
3. filter_calib 单 nonce 耗时 99s；候选到达率 ~127/h（4 卡），5 路并行验证足够
4. FW52 profile：WDIV/WMUL 与基线零差异；FOLDD/FOLDM 每轮恰好 -1（基线 53/54 → 52/53）
   - 生成：`SUB4_PP_DUMP_WIDTHS=1 PP_REPLAY_FOLD_WINDOW=52 PP_REPLAY_FOLD_WINDOW_MUL=53 build_circuit 2>&1 >/dev/null | grep '^W '`
   - fast_grind 已加运行时表选择（`fw52tab` 模块 + `fw52_fold()` OnceLock），新增表文件 `fast_filter_tables_fw52.inc`
   - fast_grind fails 对残余只建模经典逃逸（6/7 C 命中，P 类全部不可见），**不能当安全筛**；生产管道直接对每个走步干净候选跑 filter_calib

## 生产管道（2026-09-11 23:25 启动）
- 4 卡驱动 `/tmp/gpu_grind_fw52.sh <gpu> <start> 400`，chunk=10M（~35min），起点 100B/200B/300B/400B
  - 日志 `/tmp/gpu_grind_g{0..3}.log`，命中 `/tmp/fw52_walkclean_g{0..3}.txt`
  - 实测 4,735 nonce/s/卡，16B 总扫描量（均值 2.5 个命中，P≥1≈92%），约 9.3 天容量
- CPU 磨机（PID 见 ps，walk_grind 0 2^48 1 64，FW52 env）继续扫低端 [0,..)，约 750/s，日志 `/tmp/fw52_grind.log`
- 验证守护 `/tmp/fw52_verify_watch.sh`：汇总所有候选 → 5 路并行 filter_calib
  - 结果 `/tmp/fw52_verify_results.log`；已处理 `/tmp/fw52_verified_done.txt`
  - **0/0/0 幸存者写入 `/tmp/fw52_TRUE_CLEAN.txt`（看到就 build_circuit + eval，然后报用户确认提交）**

## 坑
- nohup `&` 方式在禁用沙箱的 shell 里启动 GPU 程序会间歇性 cudaMalloc "OS call failed"
  （CUDA 拦截被沙箱污染）；必须用工具自身的 run_in_background + dangerouslyDisableSandbox 逐卡启动
- filter_calib 结果行：`summary: avgT=... classical=N phase=N ancilla=0`；C/P 行给 shot 索引
