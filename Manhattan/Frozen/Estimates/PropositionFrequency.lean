import Manhattan.Model.FiberInstance
import Manhattan.Estimates.Elementary
import Manhattan.Operator.Frequency
import Manhattan.Glue.SectorEnergy

/-! Frozen Proposition 2.2 fixed-frequency anchor. -/

noncomputable section

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Estimates.proposition_frequency :
    ∃ D : Manhattan.Operator.FiberEnvironment Manhattan.WalshL2,
      D.shift = Manhattan.environmentShift ∧
      D.omega = Manhattan.originSignMultiplier ∧
      ∃ r0 C : ℝ, 0 < r0 ∧ r0 < 1 ∧ 0 ≤ C ∧
        ∀ (lambda : ℝ), ∀ hlambda : 0 < lambda, lambda ≤ 1 →
          ∀ p : Fin 2 → ℝ,
            p 0 ∈ Manhattan.Estimates.torus →
            p 1 ∈ Manhattan.Estimates.torus →
            ∃ g : Manhattan.WalshL2,
              (D.dissipativeSkewPair p).hEnergy lambda g +
                  (D.dissipativeSkewPair p).hMinusEnergy
                    hlambda (Manhattan.walshL2 ∅ - D.fiberA p g) ≤
                C * Manhattan.Operator.frequencyMajorant r0 lambda p
-- FROZEN-STATEMENT-END
:= Manhattan.Glue.proposition_frequency_v2
