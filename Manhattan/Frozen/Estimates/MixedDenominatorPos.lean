import Manhattan.Estimates.Elementary

/-! Frozen proved elementary estimate. -/

noncomputable section

open MeasureTheory Set

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Estimates.mixed_denominator_pos : ∀ {q : Manhattan.Estimates.Parameters},
  0 < q.lambda → ∀ (r beta : ℝ), 0 < q.lambda + Manhattan.Estimates.dispersion r + Manhattan.Estimates.dispersion beta
-- FROZEN-STATEMENT-END
:= @Manhattan.Estimates.mixed_denominator_pos
