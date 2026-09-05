import Manhattan.Estimates.RankOne

/-!
# Fourier--Walsh raising in Finset coordinates

A degree-`n` coefficient is indexed directly by an `n`-element Finset of
line indices. Consequently no tuple symmetrization, factorial normalization,
projection `Π_n`, raw tilde operator, or distinct-index correction lemma is
present in this module.

Paper: `manuscript.tex:1179-1205`; The Finset convention replaces the bookkeeping in
`manuscript.tex:1212-1235`.
-/

namespace Manhattan.Estimates

noncomputable section

/-- A line index has a direction (`0` for a row, `1` for a column). -/
class HasDirection (ι : Type*) where
  direction : ι → Fin 2

/-- The degree of a coefficient indexed by a Finset of distinct line indices. -/
def coefficientDegree {ι : Type*} (S : Finset ι) : ℕ := S.card

/-- The raising formula in the Finset convention Finset form.
The output is evaluated on the resulting Finset `S`; deleting `j` supplies
the input coefficient. Since `S` is a Finset, coincident line indices are
unrepresentable and no projection is required. The tuple formula's
`1/(n+1)` symmetrization factor is absent because a Finset has no slots.
-/
noncomputable def raiseCoefficient {ι : Type*} [DecidableEq ι] [HasDirection ι]
    (P : Fin 2 → ℝ) (f : Finset ι → ℂ) (S : Finset ι) : ℂ :=
  Complex.I * ∑ j ∈ S,
    (Real.sin (P (HasDirection.direction j)) : ℂ) * f (S.erase j)

/-- Lemma 5.1 in Finset form: the raising operator is the unnormalized deletion sum. -/
theorem raising_formula_finset {ι : Type*} [DecidableEq ι] [HasDirection ι]
    (P : Fin 2 → ℝ) (f : Finset ι → ℂ) (S : Finset ι) :
    raiseCoefficient P f S = Complex.I * ∑ j ∈ S,
      (Real.sin (P (HasDirection.direction j)) : ℂ) * f (S.erase j) := rfl

/-- Deleting an index lowers the Finset degree by one. -/
theorem coefficientDegree_erase {ι : Type*} [DecidableEq ι]
    {S : Finset ι} {j : ι} (hj : j ∈ S) :
    coefficientDegree (S.erase j) + 1 = coefficientDegree S := by
  exact Finset.card_erase_add_one hj

/-- Multipliers depending only on total frequency act diagonally and do not
alter the Finset support. This is the replacement for the projection
commutation clause in Lemma 5.1. -/
def totalFrequencyMultiplier {ι : Type*} (N : (Fin 2 → ℝ) → ℂ)
    (total : Finset ι → Fin 2 → ℝ) (f : Finset ι → ℂ) : Finset ι → ℂ :=
  fun S => N (total S) * f S

theorem totalFrequencyMultiplier_apply {ι : Type*} (N : (Fin 2 → ℝ) → ℂ)
    (total : Finset ι → Fin 2 → ℝ) (f : Finset ι → ℂ) (S : Finset ι) :
    totalFrequencyMultiplier N total f S = N (total S) * f S := rfl

end

end Manhattan.Estimates
