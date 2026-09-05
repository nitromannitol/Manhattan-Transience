import Manhattan.Operator.Semigroup

/-! Frozen proved semigroup statement. -/

noncomputable section

open ComplexConjugate InnerProductSpace MeasureTheory NormedSpace RCLike
open scoped ComplexConjugate InnerProduct

universe u_1

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Operator.operatorSemigroup_hasDerivAt : ∀ {E : Type u_1} [_inst : NormedAddCommGroup E]
  [_inst_1 : InnerProductSpace ℂ E] [CompleteSpace E] (G : E →L[ℂ] E) (u : E) (t : ℝ),
  HasDerivAt (fun s => (Manhattan.Operator.operatorSemigroup G s) u) (G ((Manhattan.Operator.operatorSemigroup G t) u))
    t
-- FROZEN-STATEMENT-END
:= @Manhattan.Operator.operatorSemigroup_hasDerivAt
