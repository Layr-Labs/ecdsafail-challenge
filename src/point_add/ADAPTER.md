# Fixed Leapfrog challenge adapter

The arithmetic source comes from optimizer commit `18996572e82c0e48c409d699b5593c68d786f0fc`. The Leapfrog adapter records its upstream L2 source at commit `48dcefa9f07af349f1561b345558541313cfc825`.

The source keeps the existing arithmetic, hooks, compile-time tables, and attribution. Namespace references move under `crate::point_add`. Compile-time table paths move under `src/point_add/leapfrog`. The original attribution remains in [leapfrog/NOTICE](leapfrog/NOTICE).

`WINNER_SETTINGS` in [mod.rs](mod.rs) contains the fixed candidate settings. These settings come from the committed `runs/frontier-exploitation-20261024/result.json` winner. Its arithmetic program is absent. The configuration map uses fixed source values.

The adapter constructs complete 256-bit secp256k1 point addition from the Rust arithmetic modules and their compile-time tables. The build emission reproduces 39,457,885 bytes with SHA-256:

```text
9271a9aa2b368b88989e905a932d5469baece5f3af00c0e928e8dcb7b9ce3c01
```

The emission is a source replay check. The study retains the circuit's qualification and official evidence. A change to the fixed settings creates a new candidate and needs its own validation.
