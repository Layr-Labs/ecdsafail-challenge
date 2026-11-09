//! Isolated K1 primitive. No frame dispatch, allocation, clean loan or measurement.
//! Lineage: bound de464 TTK ladder and dirty V-chain, with literal sum writes.
use super::builder::{B, G};
use crate::circuit::QubitId;
use std::collections::BTreeMap;

#[derive(Clone, Copy, Debug)]
pub(crate) struct Literal {
    pub wire: QubitId,
    pub positive: bool,
}
#[derive(Clone, Debug)]
pub(crate) enum Enable {
    One,
    // Contract admits exactly one or two retained signed literals.
    Literals(Vec<Literal>),
    // Exact source native enable: signed flag AND NOT(PH AND C).
    Native {
        flag: Literal,
        ph: QubitId,
        c: QubitId,
    },
}
impl Enable {
    // DESIGN section 4: negative native flag is conjugated once around the
    // complete arithmetic operation, including the high-slice correction.
    fn native_polarity(&self, nonempty: bool) -> (Self, Option<QubitId>) {
        match self {
            Self::Native { flag, ph, c } if !flag.positive => (
                Self::Native {
                    flag: Literal {
                        wire: flag.wire,
                        positive: true,
                    },
                    ph: *ph,
                    c: *c,
                },
                if nonempty { Some(flag.wire) } else { None },
            ),
            _ => (self.clone(), None),
        }
    }
    fn wires(&self) -> Vec<QubitId> {
        match self {
            Self::One => vec![],
            Self::Literals(v) => v.iter().map(|x| x.wire).collect(),
            Self::Native { flag, ph, c } => vec![flag.wire, *ph, *c],
        }
    }
    pub(crate) fn donors_needed(&self) -> usize {
        match self {
            Self::One => 0,
            Self::Literals(v) => v.len().saturating_sub(1),
            Self::Native { .. } => 2,
        }
    }
    fn terms(&self) -> Vec<Vec<Literal>> {
        match self {
            Self::One => vec![vec![]],
            Self::Literals(v) => vec![v.clone()],
            Self::Native { flag, ph, c } => vec![
                vec![*flag],
                vec![
                    *flag,
                    Literal {
                        wire: *ph,
                        positive: true,
                    },
                    Literal {
                        wire: *c,
                        positive: true,
                    },
                ],
            ],
        }
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Role {
    Source,
    Target,
    Padding,
    Control,
    Donor,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum ContractError {
    Width,
    EnableShape,
    Alias {
        first: Role,
        second: Role,
        wire: u64,
    },
    Held {
        role: Role,
        wire: u64,
    },
    Forbidden {
        role: Role,
        wire: u64,
    },
    DonorCapacity {
        needed: usize,
        supplied: usize,
    },
}
#[derive(Clone, Copy)]
pub(crate) struct Exclusions<'a> {
    // Caller owns this list; primitive never infers a clean value or filters an alias.
    pub held: &'a [QubitId],
    pub forbidden: &'a [QubitId],
}
fn validate(
    a: &[QubitId],
    target: &[QubitId],
    padding: &[QubitId],
    f: &Enable,
    donors: &[QubitId],
    exclude: Exclusions<'_>,
) -> Result<(), ContractError> {
    if target.len() != a.len() + padding.len() {
        return Err(ContractError::Width);
    }
    if matches!(f, Enable::Literals(v) if !(1..=2).contains(&v.len())) {
        return Err(ContractError::EnableShape);
    }
    let controls = f.wires();
    let mut used = BTreeMap::new();
    for (role, lanes) in [
        (Role::Source, a),
        (Role::Target, target),
        (Role::Padding, padding),
        (Role::Control, controls.as_slice()),
        (Role::Donor, donors),
    ] {
        for q in lanes {
            if exclude.forbidden.contains(q) {
                return Err(ContractError::Forbidden { role, wire: q.0 });
            }
            if exclude.held.contains(q) {
                return Err(ContractError::Held { role, wire: q.0 });
            }
            if let Some(first) = used.insert(q.0, role) {
                return Err(ContractError::Alias {
                    first,
                    second: role,
                    wire: q.0,
                });
            }
        }
    }
    let needed = if target.is_empty() {
        0
    } else {
        f.donors_needed()
    };
    if donors.len() < needed {
        return Err(ContractError::DonorCapacity {
            needed,
            supplied: donors.len(),
        });
    }
    Ok(())
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Mutation {
    None,
    #[cfg(test)]
    DropCorrection,
    #[cfg(test)]
    ForwardCorrection,
    #[cfg(test)]
    MismatchedEnable,
    #[cfg(test)]
    TruncatedTarget,
    #[cfg(test)]
    MissingDirtyEcho,
    #[cfg(test)]
    MissingNativeOffTerm,
}
fn literal(
    b: &mut B,
    terms: &[Literal],
    source: QubitId,
    target: QubitId,
    donors: &[QubitId],
    mutation: Mutation,
) {
    for lit in terms {
        if !lit.positive {
            b.x(lit.wire);
        }
    }
    let mut controls: Vec<_> = terms.iter().map(|lit| lit.wire).collect();
    controls.push(source);
    #[cfg(test)]
    if mutation == Mutation::MissingDirtyEcho && controls.len() >= 3 {
        b.begin();
        super::mask::mcx_dirty(b, &controls, target, donors);
        let mut damaged = b.end();
        assert!(damaged.pop().is_some());
        b.play(&damaged, false);
    } else {
        super::mask::mcx_dirty(b, &controls, target, donors);
    }
    #[cfg(not(test))]
    {
        let _ = mutation;
        super::mask::mcx_dirty(b, &controls, target, donors);
    }
    for lit in terms.iter().rev() {
        if !lit.positive {
            b.x(lit.wire);
        }
    }
}
fn sum_write(
    b: &mut B,
    a: QubitId,
    target: QubitId,
    f: &Enable,
    donors: &[QubitId],
    mutation: Mutation,
) {
    let terms = f.terms();
    for (i, term) in terms.iter().enumerate() {
        #[cfg(test)]
        if mutation == Mutation::MissingNativeOffTerm
            && matches!(f, Enable::Native { .. })
            && i == 1
        {
            continue;
        }
        let _ = i;
        literal(b, term, a, target, donors, mutation);
    }
}
// Exact arith.rs:94-133 ordering, with only wr replaced. Width 0/1 are explicit.
fn add_unchecked(
    b: &mut B,
    a: &[QubitId],
    t: &[QubitId],
    f: &Enable,
    donors: &[QubitId],
    mutation: Mutation,
) {
    let n = t.len();
    if n == 0 {
        return;
    }
    if n == 1 {
        sum_write(b, a[0], t[0], f, donors, mutation);
        return;
    }
    for i in 1..n {
        b.cx(a[i], t[i]);
    }
    for i in (1..n - 1).rev() {
        b.cx(a[i], a[i + 1]);
    }
    for i in 0..n - 1 {
        b.ccx(t[i], a[i], a[i + 1]);
    }
    for i in (1..n).rev() {
        sum_write(b, a[i], t[i], f, donors, mutation);
        b.ccx(t[i - 1], a[i - 1], a[i]);
    }
    for i in 1..n - 1 {
        b.cx(a[i], a[i + 1]);
    }
    sum_write(b, a[0], t[0], f, donors, mutation);
    for i in 1..n {
        b.cx(a[i], t[i]);
    }
}
pub(crate) fn add_f(
    b: &mut B,
    a: &[QubitId],
    target: &[QubitId],
    f: &Enable,
    donors: &[QubitId],
    exclude: Exclusions<'_>,
) -> Result<Vec<G>, ContractError> {
    validate(a, target, &[], f, donors, exclude)?;
    let (f, flip) = f.native_polarity(!target.is_empty());
    b.begin();
    if let Some(q) = flip {
        b.x(q);
    }
    add_unchecked(b, a, target, &f, donors, Mutation::None);
    if let Some(q) = flip {
        b.x(q);
    }
    Ok(b.end())
}
pub(crate) fn pad_add_f(
    b: &mut B,
    a: &[QubitId],
    target: &[QubitId],
    padding: &[QubitId],
    f: &Enable,
    donors: &[QubitId],
    exclude: Exclusions<'_>,
) -> Result<Vec<G>, ContractError> {
    pad_impl(b, a, target, padding, f, donors, exclude, Mutation::None)
}
fn pad_impl(
    b: &mut B,
    a: &[QubitId],
    target: &[QubitId],
    padding: &[QubitId],
    f: &Enable,
    donors: &[QubitId],
    exclude: Exclusions<'_>,
    mutation: Mutation,
) -> Result<Vec<G>, ContractError> {
    validate(a, target, padding, f, donors, exclude)?;
    let (normalized, flip) = f.native_polarity(!target.is_empty());
    let f = &normalized;
    b.begin();
    if let Some(q) = flip {
        b.x(q);
    }
    #[cfg(test)]
    if mutation == Mutation::TruncatedTarget {
        add_unchecked(b, a, &target[..a.len()], f, donors, Mutation::None);
        if let Some(q) = flip {
            b.x(q);
        }
        return Ok(b.end());
    }
    let mut extended = a.to_vec();
    extended.extend_from_slice(padding);
    add_unchecked(b, &extended, target, f, donors, mutation);
    let correction_enable = f.clone();
    #[cfg(test)]
    let correction_enable = if mutation == Mutation::MismatchedEnable {
        match f {
            Enable::Literals(v) if v.len() == 2 => Enable::Literals(v[..1].to_vec()),
            _ => panic!("mismatched-enable fixture requires two literals"),
        }
    } else {
        correction_enable
    };
    b.begin();
    add_unchecked(
        b,
        padding,
        &target[a.len()..],
        &correction_enable,
        donors,
        mutation,
    );
    let correction = b.end();
    #[cfg(test)]
    if mutation != Mutation::DropCorrection {
        b.play(&correction, mutation != Mutation::ForwardCorrection);
    }
    #[cfg(not(test))]
    b.play(&correction, true);
    if let Some(q) = flip {
        b.x(q);
    }
    Ok(b.end())
}
#[cfg(test)]
pub(crate) fn mutant_record(
    b: &mut B,
    a: &[QubitId],
    target: &[QubitId],
    padding: &[QubitId],
    f: &Enable,
    donors: &[QubitId],
    exclude: Exclusions<'_>,
    mutation: Mutation,
) -> Result<Vec<G>, ContractError> {
    pad_impl(b, a, target, padding, f, donors, exclude, mutation)
}
