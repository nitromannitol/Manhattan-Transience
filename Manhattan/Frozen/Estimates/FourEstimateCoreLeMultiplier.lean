import Manhattan.Estimates.RankOne

/-! Frozen proved explicit estimate. -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Estimates.fourEstimateCore_le_multiplier : ∀ {q : Manhattan.Estimates.Parameters},
  0 ≤ q.lambda → ∀ (P : Fin 2 → ℝ), Manhattan.Estimates.fourEstimateCore q P ≤ Manhattan.Estimates.multiplier 40 q P
-- FROZEN-STATEMENT-END
:= @Manhattan.Estimates.fourEstimateCore_le_multiplier
