import Manhattan.Estimates.DegreeOne

/-! Frozen proved explicit estimate. -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Estimates.sin_ne_zero_on_support : ∀ {q : Manhattan.Estimates.Parameters} {a r : ℝ},
  0 < q.K * q.delta a → q.r0 < Real.pi → r ∈ q.supportInterval a → Real.sin r ≠ 0
-- FROZEN-STATEMENT-END
:= @Manhattan.Estimates.sin_ne_zero_on_support
