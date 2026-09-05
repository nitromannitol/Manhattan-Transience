import Manhattan.Glue.Fiberwise

/-! Frozen pointwise-fiber successor of Proposition 2.1. -/

noncomputable section

open MeasureTheory UnitAddTorus
open scoped ENNReal

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Operator.proposition_generator_v2 :
    ∃ D : Manhattan.Operator.FiberEnvironment Manhattan.WalshL2,
      D.shift = Manhattan.environmentShift ∧
      D.omega = Manhattan.originSignMultiplier ∧
      (∀ p : Fin 2 → ℝ,
        D.fiberGenerator p = D.fiberS p + D.fiberA p) ∧
      (∀ t : UnitAddTorus (Fin 2),
        Manhattan.Glue.torusFiberGenerator t =
          D.fiberGenerator (Manhattan.Glue.torusFrequency t)) ∧
      Manhattan.Glue.concreteJointFiberOperator =
        Manhattan.Glue.concreteFiberDirectIntegral ∧
      ∀ (lambda : ℝ), ∀ hlambda : 0 < lambda,
        (∫⁻ s in Set.Ici 0,
          ENNReal.ofReal (Real.exp (-lambda * s)) *
            Manhattan.annealedContinuousKernel s 0 0) =
          ENNReal.ofReal
            (Manhattan.Estimates.torusIntegral fun p₁ : ℝ ↦
              Manhattan.Estimates.torusIntegral fun p₂ : ℝ ↦
                (D.dissipativeSkewPair ![p₁, p₂]).resolventQuadratic
                  hlambda (Manhattan.walshL2 ∅))
-- FROZEN-STATEMENT-END
:= Manhattan.Glue.proposition_generator_v2
