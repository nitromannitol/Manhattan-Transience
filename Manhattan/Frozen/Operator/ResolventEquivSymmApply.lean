import Manhattan.Operator.Semigroup

/-! Frozen proved semigroup statement. -/

noncomputable section

open ComplexConjugate InnerProductSpace MeasureTheory NormedSpace RCLike
open scoped ComplexConjugate InnerProduct

universe u_1

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Operator.resolventEquiv_symm_apply : ∀ {E : Type u_1} [_inst : NormedAddCommGroup E]
  [_inst_1 : InnerProductSpace ℂ E] [_inst_2 : CompleteSpace E] (G : E →L[ℂ] E) {lambda : ℝ} (hlambda : 0 < lambda)
  (u : E) (hcontract : ∀ (t : ℝ), 0 ≤ t → ‖Manhattan.Operator.operatorSemigroup G t‖ ≤ 1),
  (Manhattan.Operator.resolventEquiv G hlambda hcontract).symm u = Manhattan.Operator.laplaceVector G lambda u
-- FROZEN-STATEMENT-END
:= @Manhattan.Operator.resolventEquiv_symm_apply
