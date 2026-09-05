import Manhattan.Estimates.Elementary

/-! Frozen proved elementary estimate. -/

noncomputable section

open MeasureTheory Set

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Estimates.dispersion_nonneg : ∀ (s : ℝ), 0 ≤ Manhattan.Estimates.dispersion s
-- FROZEN-STATEMENT-END
:= @Manhattan.Estimates.dispersion_nonneg
