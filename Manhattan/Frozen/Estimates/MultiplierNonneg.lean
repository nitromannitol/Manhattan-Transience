import Manhattan.Estimates.RankOne

/-! Frozen proved explicit estimate. -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Estimates.multiplier_nonneg : ∀ {kappa : ℝ} {q : Manhattan.Estimates.Parameters},
  0 ≤ kappa → 0 ≤ q.lambda → ∀ (P : Fin 2 → ℝ), 0 ≤ Manhattan.Estimates.multiplier kappa q P
-- FROZEN-STATEMENT-END
:= @Manhattan.Estimates.multiplier_nonneg
