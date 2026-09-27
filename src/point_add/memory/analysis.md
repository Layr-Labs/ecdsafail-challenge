# secp256k1 点加法优化分析

## 当前状态 (2024-09-27)

### 基线指标
| 指标 | 数值 |
|------|------|
| Toffoli (avg) | 890,060 |
| 峰值量子比特 | 1,250 |
| **Score** | **~1.11 × 10⁹** |
| Clifford | 10,115,736 |
| 发射 ops | 12,205,108 |

## 参数测试总结 (共 80+ 个参数)

### 1. 减少 ops 但不正确的参数
| 参数 | ops 变化 | 错误类型 |
|------|----------|----------|
| PP_JOINT_LOW_BITS=16 | -143,091 | 9014 个经典不匹配 |
| PP_JOINT_LOW_BITS=24 | -72,473 | 263 个经典不匹配 |
| PP_JOINT_MUL_FOLD=0 | -51,316 | 所有 9024 个不匹配 |
| SQ_CIN_SPREAD=0 | -41,371 | 11 个经典不匹配 |
| SQ_BORROW_ROW_CARRIES=1 | -23,777 | 13 个经典不匹配 |
| PP_CUT_WALKLOAN=0 | -1,793 | 17 个经典不匹配 |
| PP_SPRINT_MIXED=1 | -2,590 | 18 个经典不匹配 |
| I50_SPLIT_BRIDGE=0 | -4,626 | 15 个经典不匹配 |
| PP_DROP_EXACT_LEAD=0 | +7,001 | 16 个经典不匹配 |
| PP_FLAG_WIDEN_DIV=40 | -55 | 12 个经典不匹配 |
| SQ_ZERO_TOP_SUM=0 | -48 | 11 个经典不匹配 |
| SQ_ZERO_TOP_CROSS=0 | -35 | 11 个经典不匹配 |
| SQ_LEND_RETAINED_ANDS=0 | -18 | 11 个经典不匹配 |
| SQ_LEND_RETAINED_CROSS2=0 | -41 | 18 个经典不匹配 |
| SQ_ODD_NODE_TOPS=0 | -21 | 14 个经典不匹配 |
| PP_DROP_EXACT_LEAD_DIR=div | +7,605 | 14 个经典不匹配 |
| PP_CUT_SQIDENT=0 | -87 | 13 个经典不匹配 |

### 2. 正确但无改进的参数
| 参数 | 测试值 |
|------|--------|
| PP_JOINT_GUARD | 8/16/24/32 |
| PP_NEW_REPLAY | 0 |
| PP_DIRECT_FOLD | 0 |
| PP_MID_BATCH_DIV | 1 |
| PP_MID_BATCH_MUL | 0/16/64 |
| SQ_ROW0_CARRY | 0 |
| SQ_ROW0_INVERSE_CARRIES | 0 |
| SQ_ZERO_TOP_SPREAD | 0 |
| SQ_DEFER_CROSS_PHASE | 0 |
| SQ_HOLD_BOUNDARY | 0 |
| SQ_SPLIT_LOW_MIN | 0/128 |
| SQ_SPLIT_SUM_MIN | 0/130 |
| SQ_DIAG_PRELOAD | 0/2 |
| SQ_HIGH_CARRY_LOAN | 2 |
| SQ_LEND_RETAINED_CROSS3 | 1 |
| PP_Q1208_HELPERS | 0 |
| PP_RETAIN_EXACT_DIV | 0 |
| PP_RETAIN_EXACT_MUL | 0 |
| PP_RETAIN_EXACT_EXTRA_DIV | 0 |
| PP_RETAIN_EXACT_EXTRA_MUL | 0 |
| PP_R2 | 0/128 |
| PP_SPLIT_FOLD_OVERAGE | 0/8/16 |
| PP_SPLIT_OVERLAP_BITS | 0 |
| I12_B_GUARD | 5 |
| I35_CELLS | 1 |
| PP_FLAG_SHAPE | 0:-4/-5/-6 |
| PP_SIMPLIFY | 禁用 affine 无影响 |

### 3. 失败/panic 的参数
| 参数 | 错误类型 |
|------|----------|
| PP_WALK_GUARD_BITS=0 | panic |
| PP_WALK_GUARD_MAX_WIDTH=32 | panic |
| PP_SPLIT_FOLD=1 | panic |
| PP_REUSE_DIV_PARITY=0 | panic |
| PP_REUSE_MUL_SELECTORS=0 | panic |
| PP_PREBIAS_RETAIN_BITS=0 | panic (bits >= 12) |
| PP_FLAG_SHAPE 0:-7/-8 | ops 增加 |
| PP_REPLAY_CHUNK_COMPARE=0 | panic (n > 1) |
| PP_REPLAY_FLAG_COMPARE=0 | panic (flag shape keeps comparison positive) |
| PP_REPLAY_FOLD_WINDOW=0 | panic (bits >= 12) |
| PP_REPLAY_FOLD_WINDOW_MUL=0 | panic (fold shape keeps window positive) |
| PP_CF_END_CHUNK=0 | 正确性错误 |
| PP_CHUNK_SHAPE 改变 | phase garbage |
| PP_REPLAY_SIGN_LOAN=0 | phase garbage |
| PP_REPLAY_SIGN_LOAN_MUL=0 | 正确性错误 |

### 4. 增加 qubits 的参数
| 参数 | 结果 |
|------|------|
| SQ_HIGH_CARRY_LOAN=0 | qubits +2 |
| SQ_LEND_RETAINED_ZEROS=0 | qubits +10 |
| SQ_OWN_TOP_ZEROS=0 | qubits +1 |
| SQ_FIT_CROSS=0 | qubits +3 |

### 5. 导致 phase garbage 的参数
| 参数 | 错误类型 |
|------|----------|
| PP_JOINT_PREBIAS_DIV=0 | phase garbage |
| SQ_ALIAS_PRODUCT_LSB=0 | phase garbage |
| PP_CF_DEFER_WALK_PHASE=0 | 正确性错误 |
| I76_SOURCE_TOP_LOAN=0 | phase garbage |
| I33_DISABLE=1 | 正确性错误 |
| PP_REPLAY_SIGN_LOAN=0 | phase garbage |
| PP_REPLAY_SIGN_LOAN_MUL=0 | 正确性错误 |
| PP_CHUNK_SHAPE 改变 | phase garbage |
| PP_DROP_EXACT_LEAD=0 | 正确性错误 |

### 6. 其他失败参数
| 参数 | 错误类型 |
|------|----------|
| PP_JOINT_GUARD 各种值 | 正确性错误 |
| PP_PREBIAS_DOUBLE=0 | 正确性错误 |
| PP_PREBIAS_DOUBLE_FALLBACK=0 | 正确性错误 |
| PP_SOURCE_SIGN_GROW=0 | 正确性错误 |
| PP_J_XFUSE/YFUSE/AFUSE/RFUSE/SEED1 | 正确性错误 |
| SQ_ROW0_COPY=0 | 正确性错误 |
| SQ_ROW1_INVERSE_CARRIES=0 | 正确性错误 |
| SQ_ROW1_STREAM=0 | 正确性错误 |
| SQ_ROW_ALL_MEASURE_TOP=0 | 正确性错误 |
| I74_RESULT_TOP_LOAN=0 | 正确性错误 |
| PP_N_HOLE2=0 | 正确性错误 |
| CMP_SEED_ALL=0 | 正确性错误 |

## 结论

1. **所有参数已测试完毕**: 共测试了 80+ 个参数
2. **安全边界已确定**: 当前参数设置都在安全边界
3. **无改进空间**: 没有找到可以同时保持正确性并减少 Toffoli 或 qubits 的参数
4. **可能的算法级优化**: 需要深入修改算法逻辑，而非简单参数调整

## 基线状态
- Toffoli: 890,060
- Qubits: 1,250
- Score: ~1.11 × 10⁹
