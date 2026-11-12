import Manhattan.Glue.Discharge
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The corrected competitor certificate of `Glue/Competitor.lean`

`Manhattan.Glue.CorrectedCompetitorCertificate` quantifies over an arbitrary Walsh
competitor, exactly as Proposition 2.2 and the row/column exchange at
`manuscript.tex:1156` require.  It is discharged here from the single shared bound.

Paper: `manuscript.tex:640-661` and `manuscript.tex:1156`.
-/

noncomputable section

open ComplexConjugate InnerProductSpace RCLike

namespace Manhattan.Glue

section Young

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

open Manhattan.Operator
open LatticeProb.Analysis

/-- Public form of the Young inequality for the dual energy: every test
vector gives a lower bound for `‖q‖²_{-1}`. -/
theorem young_hMinusEnergy (P : DissipativeSkewPair E) {lambda : ℝ}
    (hlambda : 0 < lambda) (q d : E) :
    2 * re ⟪q, d⟫_ℂ - P.hEnergy lambda d ≤ P.hMinusEnergy hlambda q := by
  let y := (P.hEquiv hlambda).symm q
  have hqy : P.H lambda y = q := P.H_apply_inverse hlambda q
  have hnonneg : 0 ≤ P.hEnergy lambda (y - d) :=
    P.hEnergy_nonneg hlambda.le (y - d)
  rw [DissipativeSkewPair.hEnergy] at hnonneg
  rw [DissipativeSkewPair.hEnergy, DissipativeSkewPair.hMinusEnergy]
  change 2 * re ⟪q, d⟫_ℂ - re ⟪P.H lambda d, d⟫_ℂ ≤ re ⟪q, y⟫_ℂ
  rw [← hqy]
  simp only [map_sub, inner_sub_left, inner_sub_right, map_sub] at hnonneg
  have hcross : re ⟪P.H lambda d, y⟫_ℂ = re ⟪P.H lambda y, d⟫_ℂ :=
    (P.re_inner_H_symm lambda d y).trans (inner_re_symm d (P.H lambda y))
  linarith

end Young

section Corrected

/-- Discharge of `CorrectedCompetitorCertificate` from the sector energy bound. -/
theorem correctedCompetitorCertificate_of_sectorEnergy {M : ℝ} (hM : 0 ≤ M)
    (h : ConcreteSectorEnergyBound M) :
    ∃ r0 C : ℝ, CorrectedCompetitorCertificate r0 C := by
  obtain ⟨C, hC, hhoriz⟩ := correctedHorizontalEnergySupply_of_sectorEnergy hM h
  refine ⟨correctedCompetitorCutoff, C + correctedLowLogConstant + 1,
    correctedCompetitorCutoff_pos, correctedCompetitorCutoff_lt_one,
    by nlinarith [correctedLowLogConstant_nonneg], ?_⟩
  exact correctedCompetitor_all_frequencies_of_horizontal C hC hhoriz

end Corrected

end Manhattan.Glue
