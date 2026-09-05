from functools import lru_cache
from typing import Literal, Optional, Sequence

from qiskit import QuantumCircuit, QuantumRegister
from qiskit.circuit import Gate, Qubit

import eea_circuit_updated as _e

# Re-export stable constants/config helpers from the original module.
C_EEA = _e.C_EEA
MEASUREMENT_UNCOMPUTE = _e.MEASUREMENT_UNCOMPUTE
N_CONFIG = _e.N_CONFIG
PRIMITIVE_OPS = _e.PRIMITIVE_OPS
paper_len_width = _e.paper_len_width
paper_shift_width = _e.paper_shift_width
Nmax_steps = _e.Nmax_steps
active_windows = _e.active_windows
get_n_config = getattr(_e, "get_n_config")
set_measurement_uncompute = _e.set_measurement_uncompute
count_circuit_ops_recursive = getattr(_e, "count_circuit_ops_recursive", None)
count_pdf_formula_all_steps = getattr(_e, "count_pdf_formula_all_steps", None)


def __getattr__(name: str):
    return getattr(_e, name)


def _scratch_for_const_endpoint(len_width: int, shift_width: int = 0) -> int:
    return max(len_width + 1, shift_width + 1)


def _scratch_for_eq(width: int) -> int:
    # compute_eq_const uses mcx_vchain over width controls and needs width-2
    # extra clean bits, plus one clean output flag supplied by the caller.
    return max(0, width - 2)


def _toggle_eq_const_under_ctrl(qc: QuantumCircuit, *, endpoint: Sequence[Qubit], const: int,
                                ctrl: Qubit, acc: Qubit, eq: Qubit, pool: Sequence[Qubit]) -> None:
    """acc ^= ctrl & [endpoint == const], restoring eq and endpoint."""
    _e.compute_eq_const(qc, endpoint, const, eq, pool)
    qc.ccx(ctrl, eq, acc)
    _e.compute_eq_const(qc, endpoint, const, eq, pool)


@lru_cache(maxsize=None)
def lc_swap_unary_gate(*, k: int, K: int, len_width: int, name: str = "LC_SWAP_S835") -> Gate:
    """Low-clean-aux location-controlled swap.

    This is semantically the same block as Section 4.4's unary selected swap,
    but uses a serial equality scan over j in [k,K] instead of keeping a unary
    path register.  The scan is gate-heavier but uses only O(log n) clean
    helper bits.
    """
    if k > K:
        raise ValueError("need k <= K")
    M = K - k + 1
    scratch_size = max(len_width + 1, 2 + _scratch_for_eq(len_width))

    Ctrl = QuantumRegister(1, "Ctrl")
    Sign = QuantumRegister(1, "Sign")
    Work1 = QuantumRegister(M, "Work1")
    l_t = QuantumRegister(len_width, "l_t")
    l_q = QuantumRegister(len_width, "l_q")
    Scratch = QuantumRegister(scratch_size, "Scratch")
    qc = _e._block_circuit(Ctrl, Sign, Work1, l_t, l_q, Scratch, name=name)

    carry = Scratch[0]
    const_scratch = list(Scratch[: len_width + 1])

    # Prepare raw J = (ell_t-1)+(ell_q-1)+3 = ell_t+ell_q+1 in l_q.
    qc.append(_e.cuccaro_add_mod_2n_no_z_gate(len_width, name="ADD_lt_to_lq"), list(l_t) + list(l_q) + [carry])
    _e.add_const_mod_2n(qc, l_q, 3, const_scratch)

    eq = Scratch[0]
    g = Scratch[1]
    pool = list(Scratch[2:])
    for j in range(k, K + 1):
        _e.compute_eq_const(qc, l_q, j, eq, pool)
        qc.ccx(Ctrl[0], eq, g)
        _e.cswap_toffoli(qc, g, Sign[0], Work1[j - k])
        qc.ccx(Ctrl[0], eq, g)
        _e.compute_eq_const(qc, l_q, j, eq, pool)

    _e.sub_const_mod_2n(qc, l_q, 3, const_scratch)
    qc.append(_e.cuccaro_sub_mod_2n_no_z_gate(len_width, name="SUB_lt_from_lq"), list(l_t) + list(l_q) + [carry])
    return _e._finalize_block(qc)


@lru_cache(maxsize=None)
def lc_interval_addsub_unary_gate(*, n: int, k: int, K: int, len_width: int, shift_width: int,
                                  mode: Literal["add", "sub"], sign_update: bool,
                                  target: Literal["work1", "work2"], name: str) -> Gate:
    """Low-clean-aux two-endpoint location-controlled Add/Sub.

    It preserves the exact endpoint logic of the original block:
      L = ell_t + ell_q + 2, R = n + 3 - ell_s.
    The active range accumulator is updated by equality tests for R and L while
    scanning the work interval.  This replaces the two simultaneous unary paths
    by one equality flag and one range accumulator.
    """
    if k > K:
        raise ValueError("need k <= K")
    M = K - k + 1
    endpoint_width = max(len_width, shift_width)
    scratch_size = max(
        endpoint_width + 1,                  # endpoint affine transforms
        3 + _scratch_for_eq(endpoint_width), # carry, active-acc, equality flag, equality pool
        4,                                   # controlled 3-control Toffoli pool
    )

    Ctrl = QuantumRegister(1, "Ctrl")
    Sign = QuantumRegister(1, "Sign")
    Work1 = QuantumRegister(M, "Work1")
    Work2 = QuantumRegister(M, "Work2")
    l_t = QuantumRegister(len_width, "l_t")
    l_q = QuantumRegister(len_width, "l_q")
    l_s = QuantumRegister(shift_width, "l_s")
    Scratch = QuantumRegister(scratch_size, "Scratch")
    qc = _e._block_circuit(Ctrl, Sign, Work1, Work2, l_t, l_q, l_s, Scratch, name=name)

    carry = Scratch[0]
    const_scratch = list(Scratch[: endpoint_width + 1])

    # Prepare raw L=(ell_t-1)+(ell_q-1)+4 and raw R=n+2-(ell_s-1).
    qc.append(_e.cuccaro_add_mod_2n_no_z_gate(len_width, name="ADD_lt_to_lq"), list(l_t) + list(l_q) + [carry])
    _e.add_const_mod_2n(qc, l_q, 4, const_scratch[: len_width + 1])
    _e.const_minus_inplace(qc, l_s, n + 2, const_scratch[: shift_width + 1])

    acc = Scratch[1]
    eq = Scratch[2]
    pool = list(Scratch[3:])

    def qpair(j: int) -> tuple[Qubit, Qubit]:
        idx = j - k
        if target == "work1":
            return Work2[idx], Work1[idx]
        if target == "work2":
            return Work1[idx], Work2[idx]
        raise ValueError("target must be 'work1' or 'work2'")

    # First pass: j = K, ..., k. Toggle active at R before the cell and at L after the cell.
    for j in range(K, k - 1, -1):
        _toggle_eq_const_under_ctrl(qc, endpoint=l_s, const=j, ctrl=Ctrl[0], acc=acc, eq=eq, pool=pool)
        addend, tgt = qpair(j)
        _e._apply_cell(qc, mode, "first", acc, addend, tgt, carry, pool)
        _toggle_eq_const_under_ctrl(qc, endpoint=l_q, const=j, ctrl=Ctrl[0], acc=acc, eq=eq, pool=pool)

    if sign_update:
        qc.cx(carry, Sign[0])

    # Second pass: j = k, ..., K. Toggle at L before the cell and at R after the cell.
    for j in range(k, K + 1):
        _toggle_eq_const_under_ctrl(qc, endpoint=l_q, const=j, ctrl=Ctrl[0], acc=acc, eq=eq, pool=pool)
        addend, tgt = qpair(j)
        _e._apply_cell(qc, mode, "second", acc, addend, tgt, carry, pool)
        _toggle_eq_const_under_ctrl(qc, endpoint=l_s, const=j, ctrl=Ctrl[0], acc=acc, eq=eq, pool=pool)

    _e.const_minus_inplace(qc, l_s, n + 2, const_scratch[: shift_width + 1])
    _e.sub_const_mod_2n(qc, l_q, 4, const_scratch[: len_width + 1])
    qc.append(_e.cuccaro_sub_mod_2n_no_z_gate(len_width, name="SUB_lt_from_lq"), list(l_t) + list(l_q) + [carry])
    return _e._finalize_block(qc)


@lru_cache(maxsize=None)
def lc_prefix_addsub_unary_gate(*, k: int, K: int, len_width: int,
                                mode: Literal["add", "sub"], sign_update: bool,
                                target: Literal["work1", "work2"], name: str) -> Gate:
    """Low-clean-aux one-endpoint prefix Add/Sub for the t-side arithmetic."""
    if k > K:
        raise ValueError("need k <= K")
    M = K - k + 1
    scratch_size = max(len_width + 1, 3 + _scratch_for_eq(len_width), 4)

    Ctrl = QuantumRegister(1, "Ctrl")
    Sign = QuantumRegister(1, "Sign")
    Work1 = QuantumRegister(M, "Work1")
    Work2 = QuantumRegister(M, "Work2")
    l_t = QuantumRegister(len_width, "l_t")
    Scratch = QuantumRegister(scratch_size, "Scratch")
    qc = _e._block_circuit(Ctrl, Sign, Work1, Work2, l_t, Scratch, name=name)

    carry = Scratch[0]
    const_scratch = list(Scratch[: len_width + 1])
    _e.add_const_mod_2n(qc, l_t, 2, const_scratch)

    acc = Scratch[1]
    eq = Scratch[2]
    pool = list(Scratch[3:])

    def qpair(j: int) -> tuple[Qubit, Qubit]:
        idx = j - k
        if target == "work1":
            return Work2[idx], Work1[idx]
        if target == "work2":
            return Work1[idx], Work2[idx]
        raise ValueError("target must be 'work1' or 'work2'")

    # First pass: decreasing. Turn active on at R; turn it off at k after the cell.
    for j in range(K, k - 1, -1):
        _toggle_eq_const_under_ctrl(qc, endpoint=l_t, const=j, ctrl=Ctrl[0], acc=acc, eq=eq, pool=pool)
        addend, tgt = qpair(j)
        _e._apply_cell(qc, mode, "first", acc, addend, tgt, carry, pool)
        if j == k:
            qc.cx(Ctrl[0], acc)

    if sign_update:
        qc.cx(carry, Sign[0])

    # Second pass: increasing. Active starts on and is turned off after R.
    qc.cx(Ctrl[0], acc)
    for j in range(k, K + 1):
        addend, tgt = qpair(j)
        _e._apply_cell(qc, mode, "second", acc, addend, tgt, carry, pool)
        _toggle_eq_const_under_ctrl(qc, endpoint=l_t, const=j, ctrl=Ctrl[0], acc=acc, eq=eq, pool=pool)

    _e.sub_const_mod_2n(qc, l_t, 2, const_scratch)
    return _e._finalize_block(qc)


@lru_cache(maxsize=None)
def len_update_lt_unary_gate(*, n: int, k: int, K: int, len_width: int, name: str = "LEN_LT_S835") -> Gate:
    """Length update for ell_t with shared endpoint/zero-map scratch."""
    if k > K:
        raise ValueError("need k <= K")
    M = K - k + 1
    depth = _e.unary_depth(M)
    scratch_size = max(len_width + 1, depth + 2)

    Ctrl = QuantumRegister(1, "Ctrl")
    Work1 = QuantumRegister(M, "Work1")
    Work2 = QuantumRegister(M, "Work2")
    l_t = QuantumRegister(len_width, "l_t")
    l_rp = QuantumRegister(len_width, "l_rp")
    Scratch = QuantumRegister(scratch_size, "Scratch")
    qc = _e._block_circuit(Ctrl, Work1, Work2, l_t, l_rp, Scratch, name=name)

    _e.const_minus_inplace(qc, l_rp, n + 2, list(Scratch[: len_width + 1]))
    _e.highest_position_xor_write(qc, ctrl=Ctrl[0], boundary_B=l_rp, bits=Work2, dirty=Work1,
                                  target_len=l_t, k=k, K=K, scratch=list(Scratch[: depth + 2]))
    _e.highest_position_xor_write(qc, ctrl=Ctrl[0], boundary_B=l_rp, bits=Work1, dirty=Work2,
                                  target_len=l_t, k=k, K=K, scratch=list(Scratch[: depth + 2]))
    _e.const_minus_inplace(qc, l_rp, n + 2, list(Scratch[: len_width + 1]))
    return _e._finalize_block(qc)


@lru_cache(maxsize=None)
def len_update_lrp_unary_gate(*, n: int, k: int, K: int, len_width: int, name: str = "LEN_LRP_S835") -> Gate:
    """Length update for ell_r' with shared endpoint/zero-map scratch."""
    if k > K:
        raise ValueError("need k <= K")
    M = K - k + 1
    depth = _e.unary_depth(M)
    scratch_size = max(len_width + 1, depth + 2)

    Ctrl = QuantumRegister(1, "Ctrl")
    Work1 = QuantumRegister(M, "Work1")
    Work2 = QuantumRegister(M, "Work2")
    l_t = QuantumRegister(len_width, "l_t")
    l_rp = QuantumRegister(len_width, "l_rp")
    Scratch = QuantumRegister(scratch_size, "Scratch")
    qc = _e._block_circuit(Ctrl, Work1, Work2, l_t, l_rp, Scratch, name=name)

    _e.add_const_mod_2n(qc, l_t, 3, list(Scratch[: len_width + 1]))
    _e.right_length_xor_write(qc, n=n, ctrl=Ctrl[0], boundary_A=l_t, bits=Work1, dirty=Work2,
                              target_len=l_rp, k=k, K=K, scratch=list(Scratch[: depth + 2]))
    _e.right_length_xor_write(qc, n=n, ctrl=Ctrl[0], boundary_A=l_t, bits=Work2, dirty=Work1,
                              target_len=l_rp, k=k, K=K, scratch=list(Scratch[: depth + 2]))
    _e.sub_const_mod_2n(qc, l_t, 3, list(Scratch[: len_width + 1]))
    return _e._finalize_block(qc)


@lru_cache(maxsize=None)
def swap_work_and_len_unary_shared_gate(*, n: int, len_width: int, k4: int, K4: int,
                                        k5: int, K5: int, name: str = "SWAP_AND_LEN_S835") -> Gate:
    """Full Work SWAP plus two serial length updates with one shared low-aux pool."""
    work_size = n + 3
    depth4 = _e.unary_depth(K4 - k4 + 1)
    depth5 = _e.unary_depth(K5 - k5 + 1)
    scratch4 = max(len_width + 1, depth4 + 2)
    scratch5 = max(len_width + 1, depth5 + 2)
    scratch_size = max(scratch4, scratch5)

    Ctrl = QuantumRegister(1, "Ctrl")
    Work1 = QuantumRegister(work_size, "Work1")
    Work2 = QuantumRegister(work_size, "Work2")
    l_t = QuantumRegister(len_width, "l_t")
    l_rp = QuantumRegister(len_width, "l_rp")
    Scratch = QuantumRegister(scratch_size, "Scratch")
    qc = _e._block_circuit(Ctrl, Work1, Work2, l_t, l_rp, Scratch, name=name)

    for i in range(work_size):
        _e.cswap_toffoli(qc, Ctrl[0], Work1[i], Work2[i])

    gate_lt = len_update_lt_unary_gate(n=n, k=k4, K=K4, len_width=len_width)
    _e._append_with_optional_clbits(qc, gate_lt, [Ctrl[0]] + list(Work1[k4 - 1:K4]) + list(Work2[k4 - 1:K4])
                                    + list(l_t) + list(l_rp) + list(Scratch[:scratch4]))

    gate_lrp = len_update_lrp_unary_gate(n=n, k=k5, K=K5, len_width=len_width)
    _e._append_with_optional_clbits(qc, gate_lrp, [Ctrl[0]] + list(Work1[k5 - 1:K5]) + list(Work2[k5 - 1:K5])
                                    + list(l_t) + list(l_rp) + list(Scratch[:scratch5]))
    return _e._finalize_block(qc)


def _r_addsub_scratch_size_lowaux(n: int, len_width: int, shift_width: int, window_size: int) -> int:
    endpoint_width = max(len_width, shift_width)
    return max(endpoint_width + 1, 3 + _scratch_for_eq(endpoint_width), 4)


def _swap_scratch_size_lowaux(len_width: int, window_size: int) -> int:
    return max(len_width + 1, 2 + _scratch_for_eq(len_width))


def _t_addsub_scratch_size_lowaux(len_width: int, window_size: int) -> int:
    return max(len_width + 1, 3 + _scratch_for_eq(len_width), 4)


def _len_update_scratch_size_lowaux(len_width: int, window_size: int) -> int:
    return max(len_width + 1, _e.unary_depth(window_size) + 2)


def qiskit_paper_aux_size(n: int, len_width: int, shift_width: int, T_max: Optional[int] = None,
                          include_algorithm1: bool = False) -> int:
    if T_max is None:
        T_max = _e.Nmax_steps(n)
    max_r = max_swap = max_t = max_l4 = max_l5 = 1
    for T in range(1, T_max + 1):
        w = _e.active_windows(n, T)
        max_r = max(max_r, w["r_addsub"][1] - w["r_addsub"][0] + 1)
        max_swap = max(max_swap, w["swap"][1] - w["swap"][0] + 1)
        max_t = max(max_t, w["t_addsub"][1] - w["t_addsub"][0] + 1)
        max_l4 = max(max_l4, w["len_update_lt"][1] - w["len_update_lt"][0] + 1)
        max_l5 = max(max_l5, w["len_update_lrp"][1] - w["len_update_lrp"][0] + 1)

    step_need = max(
        shift_width + 4,  # pre/post shift unchanged
        _r_addsub_scratch_size_lowaux(n, len_width, shift_width, max_r) + 2,  # preserve current reserved tmp controls
        _swap_scratch_size_lowaux(len_width, max_swap),
        _t_addsub_scratch_size_lowaux(len_width, max_t) + 1,
        max(len_width, shift_width) + 3,  # phase update unchanged
        _len_update_scratch_size_lowaux(len_width, max(max_l4, max_l5)),
        len_width - 1 + 2,
        max(len_width, shift_width) + 6,
    )
    if include_algorithm1:
        # The n+2 Algorithm-1 setup scratch would be too large for the point-addition
        # shared layout.  In the shared EEA bridge, Algorithm-1 preprocessing uses
        # no-extra clean constant/comparison helpers from under1000_modular_arithmetic_base,
        # not this full standalone paper aux path.
        step_need = max(step_need, max(len_width, shift_width) + 6)
    return step_need


def patch_original_module() -> None:
    """Patch eea_circuit_updated in-place so its scheduler calls the low-aux gates."""
    _e.lc_swap_unary_gate = lc_swap_unary_gate
    _e.lc_interval_addsub_unary_gate = lc_interval_addsub_unary_gate
    _e.lc_prefix_addsub_unary_gate = lc_prefix_addsub_unary_gate
    _e.len_update_lt_unary_gate = len_update_lt_unary_gate
    _e.len_update_lrp_unary_gate = len_update_lrp_unary_gate
    _e.swap_work_and_len_unary_shared_gate = swap_work_and_len_unary_shared_gate
    _e.qiskit_paper_aux_size = qiskit_paper_aux_size


# Ensure any caller using eea_circuit_updated.append_one_step_T through this
# module sees the low-aux gate factories in that function's global namespace.
patch_original_module()

# Public aliases that intentionally come from the patched original module.
make_global_registers = _e.make_global_registers
append_one_step_T = _e.append_one_step_T
build_steps_circuit_streamed = getattr(_e, "build_steps_circuit_streamed", None)
build_modular_inversion_algorithm1_circuit = getattr(_e, "build_modular_inversion_algorithm1_circuit", None)


if __name__ == "__main__":
    import argparse, json
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=256)
    args = ap.parse_args()
    cfg = get_n_config(args.n)
    print(json.dumps({
        "n": args.n,
        "len_width": cfg["len_width"],
        "shift_width": cfg["shift_width"],
        "T_max": cfg["T_max"],
        "lowaux_step_aux": qiskit_paper_aux_size(args.n, cfg["len_width"], cfg["shift_width"], cfg["T_max"]),
    }, indent=2))
