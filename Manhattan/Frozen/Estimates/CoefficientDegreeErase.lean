import Manhattan.Estimates.FinsetRaising

/-! Frozen proved explicit estimate. -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

universe u_1

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Estimates.coefficientDegree_erase : ∀ {ι : Type u_1} [_inst : DecidableEq ι] {S : Finset ι} {j : ι},
  j ∈ S → Manhattan.Estimates.coefficientDegree (S.erase j) + 1 = Manhattan.Estimates.coefficientDegree S
-- FROZEN-STATEMENT-END
:= @Manhattan.Estimates.coefficientDegree_erase
