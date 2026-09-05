import Manhattan.Operator.Frequency

/-! Frozen torus-restricted successor of the fixed-frequency consequence. -/

noncomputable section

open MeasureTheory
open scoped BigOperators

universe u_1

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Operator.frequency_resolvent_le_of_competitor_v2 :
    ∀ {E : Type u_1} [_inst : NormedAddCommGroup E]
      [_inst_1 : InnerProductSpace ℂ E] [_inst_2 : CompleteSpace E]
      (D : Manhattan.Operator.FiberEnvironment E) (V : E),
      Manhattan.Operator.CompetitorBoundClaimV2 D V →
        ∃ r0 C : ℝ, 0 < r0 ∧ r0 < 1 ∧ 0 ≤ C ∧
          ∀ (lambda : ℝ) (hlambda : 0 < lambda), lambda ≤ 1 →
            ∀ p : Fin 2 → ℝ,
              p 0 ∈ Manhattan.Operator.frequencyTorus →
              p 1 ∈ Manhattan.Operator.frequencyTorus →
              (D.dissipativeSkewPair p).resolventQuadratic hlambda V ≤
                C * Manhattan.Operator.frequencyMajorant r0 lambda p
-- FROZEN-STATEMENT-END
:= @Manhattan.Operator.frequency_resolvent_le_of_competitor_v2
