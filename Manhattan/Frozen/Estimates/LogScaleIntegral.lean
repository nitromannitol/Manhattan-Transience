import Manhattan.Estimates.Elementary

/-! Frozen proved elementary estimate. -/

noncomputable section

open MeasureTheory Set

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Estimates.logScaleIntegral : ∀ {a b : ℝ},
  0 < a → a ≤ b → ∫ (r : ℝ) in a..b, (r * √(1 + Real.log (b / r)))⁻¹ = 2 * (√(1 + Real.log (b / a)) - 1)
-- FROZEN-STATEMENT-END
:= @Manhattan.Estimates.logScaleIntegral
