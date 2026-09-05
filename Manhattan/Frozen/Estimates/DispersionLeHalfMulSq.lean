import Manhattan.Estimates.Elementary

/-! Frozen proved elementary estimate. -/

noncomputable section

open MeasureTheory Set

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Estimates.dispersion_le_half_mul_sq : ∀ (s : ℝ), Manhattan.Estimates.dispersion s ≤ 1 / 2 * s ^ 2
-- FROZEN-STATEMENT-END
:= @Manhattan.Estimates.dispersion_le_half_mul_sq
