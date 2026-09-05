/-
The lowering formulas of `lem:formulas`, as printed.

Two of the three are already the Lean statements: `eq:D2a` is
`Manhattan.Glue.rawD2StarTwoRow` and the first formula of `eq:D1` is
`Manhattan.Glue.dStarZero_degreeOneRealFrequency`, both matching the manuscript
including the sign.

The third, `eq:D2b`, carries a `√2` that `Manhattan.Glue.rawD2StarMixed` does
not.  That is a normalization difference and not a discrepancy: the manuscript
normalizes a type-`(1,1,2)` coefficient by `√2` so that the correspondence
between coefficients and elements is an isometry, whereas the Finset convention
used here puts the factor in the kernel instead.  In the manuscript's own
normalization the printed identity holds, which is what this file records.
-/
import Manhattan.Glue.ProjectionDischarge
import Manhattan.Glue.RaisingEnergy
import Manhattan.Glue.ConcreteRaisingFourier

namespace Manhattan.Paper

open Manhattan Manhattan.Glue

/-- **`eq:D2b` of `lem:formulas`, as printed.**  In the manuscript's
normalization, where a type-`(1,1,2)` coefficient carries the isometry factor
`√2`, the mixed lowering component is `-i√2 sin(β) ∫ k dm(r')`. -/
theorem d2StarMixed_paper (k : ℝ → ℝ → ℝ → ℂ) (r beta : ℝ) :
    (Real.sqrt 2 : ℂ) * rawD2StarMixed k r beta
      = -Complex.I * (Real.sqrt 2 : ℂ) * (Real.sin beta : ℂ) *
          Estimates.torusIntegral (fun r' => k r r' beta) := by
  rw [rawD2StarMixed]
  ring

/-- **`eq:D2a` of `lem:formulas`, as printed.**  The column component is
`-i sin(α) ∫ k dm(β)`, with no normalization factor. -/
theorem d2StarTwoRow_paper (p₂ : ℝ) (k : ℝ → ℝ → ℝ → ℂ) (r r' : ℝ) :
    rawD2StarTwoRow p₂ k r r'
      = -Complex.I * (Real.sin (mixedAlpha p₂ r r') : ℂ) *
          Estimates.torusIntegral (fun beta => k r r' beta) := by
  rw [rawD2StarTwoRow]

/-! ## `lem:raise`, and what carries its two halves

The manuscript writes the raising operator as

    `(D̃_n f)_{j₁…j_{n+1}} = (i/(n+1)) ∑_{a=1}^{n+1} sin(P_{j_a}) f_{j₁…ĵ_a…j_{n+1}}`,

a sum over the `n+1` slots the new sign can occupy, each term carrying the
symbol `i sin` at the total frequency and omitting the `a`-th index.  Both
halves of that are theorems here, at the degree the development uses.

The per-slot symbol is `Manhattan.Glue.raisingSymbol_apply`, which is exactly
`i sin(P_i)`; the sum over slots, projected to the ordered representative, is
the statement below.  The averaging factor `1/(n+1)` is not written explicitly
because it is carried by the projection to sorted representatives rather than
by the coefficient. -/

/-- **The slot sum of `eq:raise`**, at `n = 3`: summing the insertions of the
raised symbol over the four slots and projecting gives the raised coefficient. -/
theorem raise_slot_sum (p : Fin 2 → ℝ) (i : Fin 2) (g : Glue.DegreeCoefficient 3) :
    Glue.orderedRepresentativeProjection 4
        (∑ r : Fin 4, Glue.insertLine 3 r i
          (Glue.walshOrdered 3 (Glue.degreeRaiseSymbol p i g)))
      = Glue.walshOrdered 4 (Glue.degreeRaiseDir p i g) :=
  Glue.orderedRepresentativeProjection_sum_insertLine p i g

end Manhattan.Paper
