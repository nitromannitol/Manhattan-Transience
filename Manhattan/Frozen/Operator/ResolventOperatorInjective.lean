import Manhattan.Operator.Semigroup

/-! Frozen proved semigroup statement. -/

noncomputable section

open ComplexConjugate InnerProductSpace MeasureTheory NormedSpace RCLike
open scoped ComplexConjugate InnerProduct

universe u_1

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Operator.resolventOperator_injective : ∀ {E : Type u_1} [_inst : NormedAddCommGroup E]
  [_inst_1 : InnerProductSpace ℂ E] [CompleteSpace E] (G : E →L[ℂ] E) {lambda : ℝ},
  0 < lambda →
    (∀ (t : ℝ), 0 ≤ t → ‖Manhattan.Operator.operatorSemigroup G t‖ ≤ 1) →
      Function.Injective ⇑(Manhattan.Operator.resolventOperator G lambda)
-- FROZEN-STATEMENT-END
:= @Manhattan.Operator.resolventOperator_injective
