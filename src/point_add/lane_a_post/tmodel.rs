// Merge lane (round 105): included at the end of truth_simplify.rs (one `include!` line), so that these items see the
// module's private truth-table types. Nothing here is called by the truth round itself.

/// Read-only view of the truth-table value model for lane A's hold pass (truth-model zeros). The model is stepped on
/// the pass's input ops; `is_zero` reports a wire the model proves zero.
pub(crate) struct TModel {
    s: Support,
}
#[allow(dead_code)]
impl TModel {
    pub(crate) fn new(pre: &[Op]) -> Self {
        Self { s: Support::new(pre) }
    }
    pub(crate) fn step(&mut self, op: &Op) {
        let _ = self.s.step(op);
    }
    pub(crate) fn is_zero(&self, q: usize) -> bool {
        self.s.qubits[q].is_zero()
    }
}

/// Lane A's streaming driver for the truth round: the same per-op logic as `simplify_with_products(ops, true)`, with
/// the ops arriving one at a time and `pre` a synthetic list with the same analyze_ops result. Used by the streamed
/// tool only.
#[allow(dead_code)]
pub(crate) fn stream_products(pre: &[Op], input: &mut dyn FnMut() -> Option<Op>, out: &mut dyn FnMut(&Op)) {
    let mut affine = AffineSupport::new(pre);
    let mut quadratic = QuadraticSupport::new(pre);
    let mut truth = Support::new(pre);
    let mut products = Some(product::Index::new(&truth, pre));
    let mut result: Vec<Op> = Vec::with_capacity(4);
    while let Some(op) = input() {
        let product_hit = products.as_mut().and_then(|index| index.before(&truth, &op));
        let affine_rewrite = affine.step(&op);
        let quadratic_rewrite = quadratic.step(&op);
        let truth_rewrite = truth.step(&op);
        if let Some(index) = &mut products {
            index.after(&truth, &op);
        }
        let rewrite = match (affine_rewrite, quadratic_rewrite) {
            (Rewrite::Keep, Rewrite::Keep) => truth_rewrite,
            (Rewrite::Keep, quadratic_proof) => quadratic_proof,
            (affine_proof, _) => affine_proof,
        };
        match (rewrite, product_hit) {
            (Rewrite::Keep, Some(hit)) => hit.emit(op, &mut result),
            (old_proof, _) => old_proof.emit(op, &mut result),
        }
        for o in result.drain(..) {
            out(&o);
        }
    }
}
