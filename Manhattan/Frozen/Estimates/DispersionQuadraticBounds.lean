import Manhattan.Estimates.Elementary

/-! Frozen proved elementary estimate. -/

noncomputable section

open MeasureTheory Set

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Estimates.dispersion_quadratic_bounds : ∀ {s : ℝ},
  |s| ≤ Real.pi →
    2 * s ^ 2 / Real.pi ^ 2 ≤ Manhattan.Estimates.dispersion s ∧ Manhattan.Estimates.dispersion s ≤ s ^ 2 / 2
-- FROZEN-STATEMENT-END
:= @Manhattan.Estimates.dispersion_quadratic_bounds
