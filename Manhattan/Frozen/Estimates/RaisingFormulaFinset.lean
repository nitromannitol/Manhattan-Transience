import Manhattan.Estimates.FinsetRaising

/-! Frozen proved explicit estimate. -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

universe u_1

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Estimates.raising_formula_finset : ∀ {ι : Type u_1} [_inst : DecidableEq ι]
  [_inst_1 : Manhattan.Estimates.HasDirection ι] (P : Fin 2 → ℝ) (f : Finset ι → ℂ) (S : Finset ι),
  Manhattan.Estimates.raiseCoefficient P f S =
    Complex.I * ∑ j ∈ S, ↑(Real.sin (P (Manhattan.Estimates.HasDirection.direction j))) * f (S.erase j)
-- FROZEN-STATEMENT-END
:= @Manhattan.Estimates.raising_formula_finset
