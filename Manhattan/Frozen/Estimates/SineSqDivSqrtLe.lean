import Manhattan.Estimates.RankOne

/-! Frozen proved explicit estimate. -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Estimates.sine_sq_div_sqrt_le : ∀ (lambda x : ℝ),
  0 ≤ lambda → Real.sin x ^ 2 / √(lambda + Manhattan.Estimates.dispersion x) ≤ 2 * √2 * |Real.sin (x / 2)|
-- FROZEN-STATEMENT-END
:= @Manhattan.Estimates.sine_sq_div_sqrt_le
