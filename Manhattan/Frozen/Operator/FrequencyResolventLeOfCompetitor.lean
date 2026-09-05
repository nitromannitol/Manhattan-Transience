import Manhattan.Operator.Frequency

/-! Frozen proved fixed-frequency statement. -/

noncomputable section

open MeasureTheory
open scoped BigOperators

universe u_1

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Operator.frequency_resolvent_le_of_competitor : ∀ {E : Type u_1} [_inst : NormedAddCommGroup E]
  [_inst_1 : InnerProductSpace ℂ E] [_inst_2 : CompleteSpace E] (D : Manhattan.Operator.FiberEnvironment E) (V : E),
  Manhattan.Operator.CompetitorBoundClaim D V →
    ∃ r0 C,
      0 < r0 ∧
        r0 < 1 ∧
          0 ≤ C ∧
            ∀ (lambda : ℝ) (hlambda : 0 < lambda),
              lambda ≤ 1 →
                ∀ (p : Fin 2 → ℝ),
                  (D.dissipativeSkewPair p).resolventQuadratic hlambda V ≤
                    C * Manhattan.Operator.frequencyMajorant r0 lambda p
-- FROZEN-STATEMENT-END
:= @Manhattan.Operator.frequency_resolvent_le_of_competitor
