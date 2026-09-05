import Manhattan.Operator.Semigroup

/-! Frozen proved semigroup statement. -/

noncomputable section

open ComplexConjugate InnerProductSpace MeasureTheory NormedSpace RCLike
open scoped ComplexConjugate InnerProduct

universe u_1

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Operator.integrableOn_resolvent_dampedOrbit : ∀ {E : Type u_1} [_inst : NormedAddCommGroup E]
  [_inst_1 : InnerProductSpace ℂ E] [CompleteSpace E] (G : E →L[ℂ] E) {lambda : ℝ},
  0 < lambda →
    ∀ (u : E),
      (∀ (t : ℝ), 0 ≤ t → ‖Manhattan.Operator.operatorSemigroup G t‖ ≤ 1) →
        MeasureTheory.IntegrableOn
          (fun t => (Manhattan.Operator.resolventOperator G lambda) (Manhattan.Operator.dampedOrbit G lambda u t))
          (Set.Ioi 0) MeasureTheory.volume
-- FROZEN-STATEMENT-END
:= @Manhattan.Operator.integrableOn_resolvent_dampedOrbit
