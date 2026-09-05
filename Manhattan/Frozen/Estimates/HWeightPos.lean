import Manhattan.Estimates.Elementary

/-! Frozen proved elementary estimate. -/

noncomputable section

open MeasureTheory Set

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Estimates.hWeight_pos : ∀ {q : Manhattan.Estimates.Parameters},
  0 < q.lambda → ∀ (P : Fin 2 → ℝ), 0 < Manhattan.Estimates.hWeight q P
-- FROZEN-STATEMENT-END
:= @Manhattan.Estimates.hWeight_pos
