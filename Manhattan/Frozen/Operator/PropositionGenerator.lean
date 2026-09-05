import Manhattan.Glue.ConcreteGreen

/-! Frozen Proposition 2.1 anchor. -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Operator.proposition_generator :
    ∃ D : Manhattan.Operator.FiberEnvironment Manhattan.WalshL2,
      D.shift = Manhattan.environmentShift ∧
      D.omega = Manhattan.originSignMultiplier ∧
      (∀ p : Fin 2 → ℝ,
        D.fiberGenerator p = D.fiberS p + D.fiberA p) ∧
      ∀ (lambda : ℝ), ∀ hlambda : 0 < lambda,
        (∫⁻ t in Ici 0,
          ENNReal.ofReal (Real.exp (-lambda * t)) *
            Manhattan.annealedContinuousKernel t 0 0) =
          ENNReal.ofReal
            (Manhattan.Estimates.torusIntegral fun p₁ : ℝ =>
              Manhattan.Estimates.torusIntegral fun p₂ : ℝ =>
                (D.dissipativeSkewPair ![p₁, p₂]).resolventQuadratic
                  hlambda (Manhattan.walshL2 ∅))
-- FROZEN-STATEMENT-END
:= Manhattan.Glue.proposition_generator
