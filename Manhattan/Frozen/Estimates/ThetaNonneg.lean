import Manhattan.Estimates.Elementary

/-! Frozen proved elementary estimate. -/

noncomputable section

open MeasureTheory Set

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Estimates.theta_nonneg : ∀ (P : Fin 2 → ℝ), 0 ≤ Manhattan.Estimates.theta P
-- FROZEN-STATEMENT-END
:= @Manhattan.Estimates.theta_nonneg
