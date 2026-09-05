import Manhattan.Operator.Semigroup

/-! Frozen proved semigroup statement. -/

noncomputable section

open ComplexConjugate InnerProductSpace MeasureTheory NormedSpace RCLike
open scoped ComplexConjugate InnerProduct

universe u_1

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Operator.dampedOrbit_norm_le : ∀ {E : Type u_1} [_inst : NormedAddCommGroup E]
  [_inst_1 : InnerProductSpace ℂ E] (G : E →L[ℂ] E) (lambda : ℝ) (u : E),
  (∀ (t : ℝ), 0 ≤ t → ‖Manhattan.Operator.operatorSemigroup G t‖ ≤ 1) →
    ∀ {t : ℝ}, 0 ≤ t → ‖Manhattan.Operator.dampedOrbit G lambda u t‖ ≤ Real.exp (-lambda * t) * ‖u‖
-- FROZEN-STATEMENT-END
:= @Manhattan.Operator.dampedOrbit_norm_le
