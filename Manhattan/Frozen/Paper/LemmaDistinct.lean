import Manhattan.Paper.LemmaDistinct

/-! Lemma 5.3 (`lem:distinct`, `manuscript.tex:1212-1221`): for a coefficient function
`K` of type `112` symmetric in its two row frequencies, without the restriction to
distinct row indices, and `k = Π₃ k̃`, the difference `Π₂ D̃₂* k̃ - D₂* k` has only a mixed
component and its squared `H⁻¹` norm is at most `6/κ` times `⟨k̃, M k̃⟩`, for every `κ > 0`
(both sides in ordered coefficients, with the factors `2!` and `3!` of `eq:iso`). -/

open MeasureTheory UnitAddTorus
open Manhattan Manhattan.Glue Manhattan.Paper

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Paper.lemma_distinct {kappa : ℝ} (hkappa : 0 < kappa) {q : Estimates.Parameters}
    (hlam : 0 < q.lambda) (p : Fin 2 → ℝ) (K : Lp ℂ 2 (LineTorusMeasure 3))
    (hK : torusPerm 3 (Equiv.swap 0 1) K = K) :
    (∀ v : Fin 2 → LineIndex, (tuplePattern v = twoRowPattern ∨
        tuplePattern v = ![Axis.vertical, Axis.vertical]) → rawLowerDifference p K v = 0) ∧
      2 * RCLike.re (inner ℂ (rawLowerDifference p K)
          (orderedMultiplier 2 p (hInvMap hlam) (rawLowerDifference p K))) ≤
        6 / kappa * (6 * RCLike.re (inner ℂ (type112Coeff K)
          (orderedMultiplier 3 p (multiplierMapC kappa q) (type112Coeff K))))
-- FROZEN-STATEMENT-END
:= Manhattan.Paper.lemma_distinct hkappa hlam p K hK
