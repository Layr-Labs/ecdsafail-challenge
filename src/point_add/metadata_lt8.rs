//! Physical lifetime coalescing primitive; its caller owns the lease proof.
//! PRE: before every active use, the other logical wire is zero. This is a
//! semantic lifetime requirement; absence of direct gate aliases alone is
//! necessary but insufficient. The Algorithm3 lease proof is separate.
use crate::circuit::{Op, OperationType, QubitId, NO_QUBIT};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct Lease {
    pub high: u64,
    pub pool: u64,
}
impl Lease {
    pub(super) fn map(self, q: QubitId) -> QubitId {
        if q == NO_QUBIT {
            return q;
        }
        QubitId(if q.0 == self.high {
            self.pool - 1
        } else if q.0 > self.high {
            q.0 - 1
        } else {
            q.0
        })
    }
    pub(super) fn role(self, op: &Op) -> u8 {
        let q = [op.q_control2.0, op.q_control1.0, op.q_target.0];
        u8::from(q.contains(&self.high)) + 2 * u8::from(q.contains(&self.pool))
    }
}
#[derive(Default, Debug)]
pub(super) struct Census {
    pub high_ops: usize,
    pub pool_ops: usize,
    pub ownership_switches: usize,
}
pub(super) fn census(ops: &[Op], lease: Lease) -> Result<Census, String> {
    if lease.high >= lease.pool {
        return Err("require high<pool for a one-hole renumbering".into());
    }
    let mut result = Census::default();
    let mut previous = 0;
    for (index, op) in ops.iter().enumerate() {
        let role = lease.role(op);
        if role == 3 {
            return Err(format!("direct high/pool gate alias at op{index}: {op:?}"));
        }
        if role == 1 && op.kind == OperationType::AppendToRegister {
            return Err("cannot remove a declared ABI qubit".into());
        }
        if role == 1 {
            result.high_ops += 1;
        }
        if role == 2 {
            result.pool_ops += 1;
        }
        if role != 0 {
            if previous != 0 && previous != role {
                result.ownership_switches += 1;
            }
            previous = role;
        }
    }
    Ok(result)
}
pub(super) fn coalesce(ops: &mut [Op], lease: Lease) -> Result<Census, String> {
    let report = census(ops, lease)?;
    for op in ops {
        op.q_control2 = lease.map(op.q_control2);
        op.q_control1 = lease.map(op.q_control1);
        op.q_target = lease.map(op.q_target);
        op.validate();
    }
    Ok(report)
}

#[cfg(test)]
#[path = "metadata_lt8_tests.rs"]
mod tests;
