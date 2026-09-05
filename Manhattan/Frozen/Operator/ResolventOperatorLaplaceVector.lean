import Manhattan.Operator.Semigroup

/-! Frozen proved semigroup statement. -/

noncomputable section

open ComplexConjugate InnerProductSpace MeasureTheory NormedSpace RCLike
open scoped ComplexConjugate InnerProduct

universe u_1

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Operator.resolventOperator_laplaceVector : ∀ {E : Type u_1} [_inst : NormedAddCommGroup E]
  [_inst_1 : InnerProductSpace ℂ E] [CompleteSpace E] (G : E →L[ℂ] E) {lambda : ℝ},
  0 < lambda →
    ∀ (u : E),
      (∀ (t : ℝ), 0 ≤ t → ‖Manhattan.Operator.operatorSemigroup G t‖ ≤ 1) →
        (Manhattan.Operator.resolventOperator G lambda) (Manhattan.Operator.laplaceVector G lambda u) = u
-- FROZEN-STATEMENT-END
:= @Manhattan.Operator.resolventOperator_laplaceVector
