import Manhattan.Operator.Semigroup

/-! Frozen proved semigroup statement. -/

noncomputable section

open ComplexConjugate InnerProductSpace MeasureTheory NormedSpace RCLike
open scoped ComplexConjugate InnerProduct

universe u_1

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Operator.generator_commutes_operatorSemigroup : ∀ {E : Type u_1} [_inst : NormedAddCommGroup E]
  [_inst_1 : InnerProductSpace ℂ E] (G : E →L[ℂ] E) (t : ℝ), Commute G (Manhattan.Operator.operatorSemigroup G t)
-- FROZEN-STATEMENT-END
:= @Manhattan.Operator.generator_commutes_operatorSemigroup
