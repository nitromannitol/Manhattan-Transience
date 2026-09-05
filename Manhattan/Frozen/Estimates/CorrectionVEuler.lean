import Manhattan.Estimates.DegreeThree

/-! Frozen proved explicit estimate. -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Estimates.correctionV_euler : ∀ {kappa : ℝ} {q : Manhattan.Estimates.Parameters} {a r beta : ℝ},
  r ∈ q.supportInterval a →
    Manhattan.Estimates.correctionB q r beta + Manhattan.Estimates.correctionSigma kappa q a r beta ≠ 0 →
      (Manhattan.Estimates.correctionB q r beta + Manhattan.Estimates.correctionSigma kappa q a r beta) *
          Manhattan.Estimates.correctionV kappa q a r beta =
        1
-- FROZEN-STATEMENT-END
:= @Manhattan.Estimates.correctionV_euler
