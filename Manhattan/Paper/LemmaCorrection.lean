import Manhattan.Glue.SummandThreeMixedBound
import Manhattan.Glue.SummandFourAssembly

/-!
# Lemma 5.4: the correction calculation, at the operator level

`lem:correction-calculation` (`manuscript.tex:1305-1420`): for the coefficient
`k = Π₃ k̃` of `eq:ktilde`, `D₂*k` has no two-row component and `eq:reduce`
holds,

    ⟨k, H₃ k⟩ + ‖D₃ k‖²₋₁ + ‖w - D₂* k‖²₋₁ ≤ C ∫_I ∫_𝕋 dm(β) dm(r) / (B + σ).

This file states and proves both clauses for the degree-three part `k_p` of
the concrete competitor of `Manhattan/Glue/Correction.lean`, with every term
written in the operators of the concrete fiber: `H` and `H⁻¹` of
`Manhattan.concreteFiberEnvironment`, the raising operator
`Manhattan.Glue.walshRaise`, and the Walsh sector projections.  The vector `w`
is the mixed component of `D₁ f_p`, which Lemma 4.1(c) identifies as
`sgn(sin p₁) 1_I(r)`; the competitor `k_p` carries the same factor
`sgn(sin p₁)` (`manuscript.tex:1138-1141`).  The right-hand side is
`Manhattan.Glue.correctionReducedIntegral`, the integral of `eq:reduce`, and the
constant `reduceConstant q = 26 + 4 · 3/(K³ρ)` depends only on `K` and `ρ`.

The proof follows the four steps of the manuscript:

* Step 1, `eq:kenergy`: `Manhattan.Glue.rawCubicMultiplierEnergy_eq_two_correctionSigmaEnergy`;
* Step 2, the vanishing two-row component and `eq:onI`:
  `Manhattan.Glue.type112DStarTwoRow_correctedLowDegreeData` and
  `Manhattan.Glue.mixedRawResidual_eq`;
* Step 3, `eq:ebound`: `Manhattan.Estimates.errorHMinusSq_le_rowOrder`, through
  `Manhattan.Glue.mixedRawResidualHMinusSq_le_reducedIntegral`;
* Step 4, the passage to distinct line indices: Lemma 5.2 at the competitor
  (`Manhattan.Glue.hThreeForm_frozen_correctionWalsh_le`,
  `Manhattan.Glue.sectorDFourForm_shiftedCorrectionWalsh_le`) and Lemma 5.3 at
  the competitor (`Manhattan.Glue.lemma_distinct_correction_sigmaEnergy`), with
  the mixed sector computed by `Manhattan.Glue.hMinusEnergy_mixedSector`.

The multiplier `M` of `eq:M` is used with `κ = 40`, the value fixed by the
construction of the competitor.  The hypothesis `K δ < r₀` is the one of
Proposition 4.2 (`prop:key`).
-/

open scoped lp
open MeasureTheory UnitAddTorus
open Manhattan Manhattan.Glue

namespace Manhattan.Paper

noncomputable section

open Manhattan.Estimates

/-- The constant of `eq:reduce` produced by the proof of Lemma 5.4; it depends
only on `K` and `ρ`. -/
def reduceConstant (q : Parameters) : ℝ :=
  26 + 4 * errorKernelConstant q

theorem reduceConstant_pos {q : Parameters} (hq : q.Admissible) : 0 < reduceConstant q := by
  have h := (errorKernelConstant_pos hq).le
  rw [reduceConstant]
  linarith

/-- With the two-row component of `D₂*k` equal to zero, `w - D₂*k` is the mixed
Walsh vector with coefficient `w - (D₂*k)₁₂`. -/
theorem type12WalshSynthesis_sub_type112DStar (p : Fin 2 → ℝ)
    (w : ℓ²(Type12Index, ℂ)) (c : ℓ²(Type112Index, ℂ))
    (hc : type112DStarTwoRow p c = 0) :
    type12WalshSynthesis w - type112DStar p c =
      type12WalshSynthesis (w - type112DStarMixed p c) := by
  rw [type112DStar, hc, map_zero, zero_add, map_sub]

/-- **`lem:correction-calculation`** (`manuscript.tex:1305-1420`), at the
operator level.  Let `k_p` be the degree-three part of the concrete competitor
and `w` the mixed component of `D₁ f_p`.  Then the two-row component of
`D₂*k_p` vanishes, and `eq:reduce` holds:
`⟨k_p, H k_p⟩ + ‖D₃ k_p‖²₋₁ + ‖w - D₂* k_p‖²₋₁` is at most
`reduceConstant q` times `∫_I ∫_𝕋 dm(β) dm(r) / (B + σ)`. -/
theorem lemma_correction_calculation {q : Parameters} (hq : q.Admissible)
    {p : Fin 2 → ℝ} (hp₂ : |p 1| ≤ |p 0|) (hsupp : q.K * q.delta |p 0| < q.r0)
    (hcert : LemmaFourTwoIntegralCertificate q (p 0) (p 1))
    (hnormalization : degreeOneNormalization q (p 0) ≠ 0) :
    type112DStarTwoRow p
        (correctedLowDegreeData hq.1 p hcert hnormalization).mixedCoefficient = 0 ∧
      (concreteFiberEnvironment.dissipativeSkewPair p).hEnergy q.lambda
          (correctedMixedVector (correctedLowDegreeData hq.1 p hcert hnormalization)) +
        (concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hq.1
          (walshSectorComponent (fun S => S.card = 4)
            (concreteFiberA p
              (correctedMixedVector (correctedLowDegreeData hq.1 p hcert hnormalization)))) +
        (concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hq.1
          (type12WalshSynthesis (type12WalshAnalysis (walshRaise p
              (correctedRowVector (correctedLowDegreeData hq.1 p hcert hnormalization)))) -
            type112DStar p
              (correctedLowDegreeData hq.1 p hcert hnormalization).mixedCoefficient) ≤
        reduceConstant q * correctionReducedIntegral q |p 0| := by
  have hlambda : 0 < q.lambda := hq.1
  have hK20 : (20 : ℝ) ≤ q.K := hq.2.2.1
  have hK : (1 : ℝ) ≤ q.K := by linarith
  have hrhopos : 0 < q.rho := hq.2.2.2.1
  have hrhopi20 : q.rho ≤ Real.pi / 20 := hq.2.2.2.2
  have hrhopi : 3 * q.rho < Real.pi := by nlinarith [Real.pi_pos]
  have ha : (0 : ℝ) ≤ |p 0| := abs_nonneg _
  have hdelta : 0 ≤ q.delta |p 0| := Glue.delta_nonneg (q := q) ha
  have hale : |p 0| < q.r0 := by
    have h1 : q.delta |p 0| ≤ q.K * q.delta |p 0| := by nlinarith
    have h2 : |p 0| ≤ q.delta |p 0| := by
      rw [Parameters.delta]
      linarith [Real.sqrt_nonneg q.lambda]
    linarith
  have hr02 := Glue.r0_le_two_rho hq
  have hw1 : 2 * q.rho + |p 1| < Real.pi := by
    have hlt : |p 1| < 2 * q.rho := lt_of_le_of_lt hp₂ (lt_of_lt_of_le hale hr02)
    nlinarith [Real.pi_pos]
  have hw2 : q.rho + |p 0| < Real.pi := by
    have hlt : |p 0| < 2 * q.rho := lt_of_lt_of_le hale hr02
    nlinarith [Real.pi_pos]
  have htwo : type112DStarTwoRow p
      (correctedLowDegreeData hq.1 p hcert hnormalization).mixedCoefficient = 0 :=
    type112DStarTwoRow_correctedLowDegreeData hlambda p hcert hnormalization
  refine ⟨htwo, ?_⟩
  have hSR : correctionSigmaEnergy q |p 0| ≤ correctionReducedIntegral q |p 0| :=
    correctionSigmaEnergy_le_reducedIntegral hlambda |p 0|
  have hraw : rawCubicMultiplierEnergy q |p 0| (p 1) = 2 * correctionSigmaEnergy q |p 0| :=
    rawCubicMultiplierEnergy_eq_two_correctionSigmaEnergy hlambda hK hrhopos.le hrhopi ha hp₂
  have hk : shiftedCorrectionWalsh (kappa := 40) (by norm_num) hlambda |p 0| (p 0) (p 1) =
      type112WalshSynthesis (type112ShiftTwist (p 0) (p 1)
        (correctionType112Coefficients (kappa := 40) (by norm_num) hlambda |p 0| (p 1))) :=
    rfl
  have h1 : (concreteFiberEnvironment.dissipativeSkewPair p).hEnergy q.lambda
      (correctedMixedVector (correctedLowDegreeData hq.1 p hcert hnormalization)) ≤
      rawCubicMultiplierEnergy q |p 0| (p 1) := by
    rw [correctedMixedVector_eq, correctedLowDegreeData_mixed_eq hlambda p hcert hnormalization]
    refine le_trans (b := hThreeForm q.lambda p
      (shiftedCorrectionWalsh (kappa := 40) (by norm_num) hlambda |p 0| (p 0) (p 1))) ?_ ?_
    · exact hEnergy_ofReal_sign_smul_le _ hlambda.le _ _
    rw [hk, hThreeForm_type112ShiftTwist_frozen]
    have hshift : hThreeForm q.lambda ![0, -(p 1)]
        (type112WalshSynthesis
          (correctionType112Coefficients (kappa := 40) (by norm_num) hlambda |p 0| (p 1))) ≤
        rawCubicHWeightEnergy q |p 0| (p 1) :=
      hThreeForm_frozen_correctionWalsh_le hlambda |p 0| (p 1)
    exact hshift.trans ((rawCubicHWeightEnergy_le_core hlambda |p 0| (p 1)).trans
      (rawCubicCoreEnergy_le_multiplier hlambda |p 0| (p 1)))
  have h2 : (concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hq.1
      (walshSectorComponent (fun S => S.card = 4)
        (concreteFiberA p
          (correctedMixedVector (correctedLowDegreeData hq.1 p hcert hnormalization)))) ≤
      8 * rawCubicMultiplierEnergy q |p 0| (p 1) := by
    change sectorDFourForm hlambda p
      (correctedMixedVector (correctedLowDegreeData hq.1 p hcert hnormalization)) ≤ _
    rw [correctedMixedVector_eq, correctedLowDegreeData_mixed_eq hlambda p hcert hnormalization]
    exact (sectorDFourForm_ofReal_sign_smul_le hlambda p _ _).trans
      (sectorDFourForm_shiftedCorrectionWalsh_le hlambda p)
  have h3 : (concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hq.1
      (type12WalshSynthesis (type12WalshAnalysis (walshRaise p
          (correctedRowVector (correctedLowDegreeData hq.1 p hcert hnormalization)))) -
        type112DStar p
          (correctedLowDegreeData hq.1 p hcert hnormalization).mixedCoefficient) ≤
      (8 + 4 * errorKernelConstant q) * correctionReducedIntegral q |p 0| := by
    rw [type12WalshSynthesis_sub_type112DStar p _ _ htwo,
      hMinusEnergy_mixedSector hq hp₂ hw1 hw2 hcert hnormalization]
    have hmain := mixedSector_energy_le hq hp₂ hw1 hw2
    have hM := mixedRawResidualHMinusSq_le_reducedIntegral hq ha hp₂
    have hproj := (lemma_distinct_correction_sigmaEnergy hlambda hK hrhopos.le hrhopi ha p
      hp₂).2
    have herr : 0 ≤ errorKernelConstant q := (errorKernelConstant_pos hq).le
    nlinarith [hmain, hM, hproj, hSR, herr]
  rw [reduceConstant]
  nlinarith [h1, h2, h3, hraw, hSR]

end

end Manhattan.Paper
