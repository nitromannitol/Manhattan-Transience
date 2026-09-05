import Manhattan.Estimates.Elementary

/-! Frozen proved elementary estimate. -/

noncomputable section

open MeasureTheory Set

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Estimates.torusIntegral_one :
    (Manhattan.Estimates.torusIntegral fun _x : ℝ => (1 : ℝ)) = 1
-- FROZEN-STATEMENT-END
:= @Manhattan.Estimates.torusIntegral_one
