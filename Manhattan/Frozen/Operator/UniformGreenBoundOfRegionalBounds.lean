import Manhattan.Operator.Frequency

/-! Frozen proved fixed-frequency statement. -/

noncomputable section

open MeasureTheory
open scoped BigOperators

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Operator.uniform_green_bound_of_regional_bounds : ∀ {green : ℝ → ℝ}
  (B : Manhattan.Operator.RegionalIntegralBounds green) {lambda : ℝ},
  0 < lambda → lambda ≤ 1 → green lambda ≤ B.smallBound + 2 * B.middleCoefficient + B.outerBound
-- FROZEN-STATEMENT-END
:= @Manhattan.Operator.uniform_green_bound_of_regional_bounds
