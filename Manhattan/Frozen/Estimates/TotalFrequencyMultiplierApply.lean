import Manhattan.Estimates.FinsetRaising

/-! Frozen proved explicit estimate. -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

universe u_1

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Estimates.totalFrequencyMultiplier_apply : ∀ {ι : Type u_1} (N : (Fin 2 → ℝ) → ℂ)
  (total : Finset ι → Fin 2 → ℝ) (f : Finset ι → ℂ) (S : Finset ι),
  Manhattan.Estimates.totalFrequencyMultiplier N total f S = N (total S) * f S
-- FROZEN-STATEMENT-END
:= @Manhattan.Estimates.totalFrequencyMultiplier_apply
