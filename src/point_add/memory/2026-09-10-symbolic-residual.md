# Additional Q834 symbolic cleanup actions

This isolated candidate extends integrated-r4's adapter, leaving q834_clean_and.rs byte-identical to the pinned Q834 source. With MIDQ_SYMBOLIC_RESIDUAL=1 it admits two existing proof-engine actions: a CCX whose outgoing target is the constant1, or whose outgoing target is one unchanged live wire XOR a known parity. The original clean-zero action and support lowerings keep priority. Multi-wire residual synthesis remains disabled.

For a live-wire action, before the original CCX the target satisfies t=(a AND b) XOR w XOR e. Measuring t in the X basis gives phase (-1)^(m*((a AND b) XOR w XOR e)). The replacement applies CZ(a,b), Z(w), and if needed a global Neg, each under the fresh outcome m; it then copies w and optional e into the reset target. This cancels the full phase and reconstructs the exact original outgoing value, including when w aliases a control. The witness is required to differ from the target and remain unchanged. For constant1 omit Z(w) and reconstruct the target with X. These are the original engine's replacement_to_wire and replacement_to_one functions.

The engine only admits these additional actions for an unconditionally active source CCX with no per-op classical guard; the existing symbolic condition must equal1. Actual output is still emitted within any surrounding source condition scopes. Witness lookup validates current immutable value IDs, excludes the target, and treats a missing/evicted identity as no proof. Every SOURCE operation is stepped exactly once. Replacement gates are not stepped as additional source events. Fresh classical IDs start above every declared or used source bit.

No qubits are added. A promoted action removes one unconditional executed Toffoli and adds measurement/Clifford work. How many opportunities exist in the full circuit is unmeasured until generation. The new feature can be explicitly disabled for byte comparison against integrated-r4.

Native adapter tests extend the existing exhaustive per-prefix comparison over all input ABI bits and independent source/new measurement streams. New cases cover positive/complemented live-wire residuals, constant1, changed/stale witnesses, dirty target admission, conditional fallback and phase preservation. The original Q834 multi-term phase tests also run unchanged. The unit test harness remains external; trusted benchmark code is not modified.

Status: source prepared; remote build, tests, byte fallback and full-circuit regression pending.
