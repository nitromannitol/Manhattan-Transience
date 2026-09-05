import Manhattan.Estimates.DegreeOne

/-! Frozen proved explicit estimate. -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Estimates.mixedResidual_eq_indicator : ∀ {q : Manhattan.Estimates.Parameters} {p₁ r : ℝ},
  0 < q.K * q.delta |p₁| →
    q.r0 < Real.pi → Manhattan.Estimates.mixedResidual q p₁ r = Manhattan.Estimates.signedSupportIndicator q p₁ r
-- FROZEN-STATEMENT-END
:= @Manhattan.Estimates.mixedResidual_eq_indicator
