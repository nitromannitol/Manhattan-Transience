import Manhattan.Estimates.Elementary

/-! Frozen proved elementary estimate. -/

noncomputable section

open MeasureTheory Set

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Estimates.logScaleIntegral_le : ∀ {a b : ℝ},
  0 < a → a ≤ b → ∫ (r : ℝ) in a..b, (r * √(1 + Real.log (b / r)))⁻¹ ≤ 2 * √(1 + Real.log (b / a))
-- FROZEN-STATEMENT-END
:= @Manhattan.Estimates.logScaleIntegral_le
