import Manhattan.Estimates.TargetStatements

/-! Frozen proved explicit estimate. -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Estimates.multiplierComparisonClaim_proved : ∀ (K rho : ℝ),
  Manhattan.Estimates.MultiplierComparisonClaim K rho
-- FROZEN-STATEMENT-END
:= @Manhattan.Estimates.multiplierComparisonClaim_proved
