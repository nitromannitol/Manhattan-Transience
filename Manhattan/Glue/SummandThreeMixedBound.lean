import Manhattan.Glue.SummandThreeMixedFourier
import Manhattan.Glue.SummandThreeTwoRow
import Manhattan.Glue.SummandsMixed

/-!
# Summand 3 of (22), discharged

`Manhattan.Glue.summandThreeBound_of_sector_bounds` reduces summand 3 to two
sector bounds. the formalization supplies the two-row one
(`Manhattan.Glue.summandThreeTwoRowSectorBound`). This file supplies the mixed
one, from the frequency-function identification of
`Manhattan/Glue/SummandThreeMixedFourier.lean` and the scalar estimates
`Manhattan.Glue.mixedRawResidualHMinusSq_le_sqrtScale` (Lemma 5.4) and
`Manhattan.Glue.lemma_distinct_correction_sigmaEnergy` (Lemma 5.3), and then
assembles the two into `Manhattan.Glue.SummandThreeBound`.

Paper: `manuscript.tex:888-940`, `manuscript.tex:1138-1141`,
`manuscript.tex:1332-1346`.
-/

open MeasureTheory Set

namespace Manhattan.Glue

noncomputable section

open Manhattan.Estimates

/-- **The mixed sector bound of summand 3, for an admissible parameter set.** -/
theorem summandThreeMixedSectorBound_of_five {q : Parameters} (hq : q.Admissible)
    {C : ℝ} {p : Fin 2 → ℝ} (hp₂ : |p 1| ≤ |p 0|)
    (hlog : q.logThreshold < q.scaleLog |p 0|)
    (hfive : PropositionFiveTwoIntegralBound 40 C q |p 0|)
    (hlambda : 0 < q.lambda)
    (hcert : LemmaFourTwoIntegralCertificate q (p 0) (p 1))
    (hnormalization : degreeOneNormalization q (p 0) ≠ 0) :
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hlambda
        (Manhattan.type12WalshSynthesis
          (Manhattan.type12WalshAnalysis
              (walshRaise p (correctedRowVector
                (correctedLowDegreeData hlambda p hcert hnormalization))) -
            Manhattan.type112DStarMixed p
              (correctedLowDegreeData hlambda p hcert hnormalization).mixedCoefficient)) ≤
      (2 * (2 + 2 * errorKernelConstant q) + 4) * C *
        Real.sqrt (q.scaleLog |p 0|) := by
  have hK20 : (20 : ℝ) ≤ q.K := hq.2.2.1
  have hKpos : (0 : ℝ) < q.K := by linarith
  have hrhopos : 0 < q.rho := hq.2.2.2.1
  have hrhopi : q.rho ≤ Real.pi / 20 := hq.2.2.2.2
  have ha : (0 : ℝ) ≤ |p 0| := abs_nonneg _
  have hr0pos : 0 < q.r0 := by
    rw [Parameters.r0]
    positivity
  have hdelta : 0 ≤ q.delta |p 0| := delta_nonneg (q := q) ha
  have hsupp := mixedSupport_of_logThreshold (q := q) (by linarith) hr0pos hlambda ha hlog
  have hale : |p 0| < q.r0 := by
    have h1 : q.delta |p 0| ≤ q.K * q.delta |p 0| := by nlinarith
    have h2 : |p 0| ≤ q.delta |p 0| := by
      rw [Parameters.delta]
      linarith [Real.sqrt_nonneg q.lambda]
    linarith
  have hr02 := r0_le_two_rho hq
  have hw1 : 2 * q.rho + |p 1| < Real.pi := by
    have hlt : |p 1| < 2 * q.rho := lt_of_le_of_lt hp₂ (lt_of_lt_of_le hale hr02)
    nlinarith [Real.pi_pos]
  have hw2 : q.rho + |p 0| < Real.pi := by
    have hlt : |p 0| < 2 * q.rho := lt_of_lt_of_le hale hr02
    nlinarith [Real.pi_pos]
  rw [hMinusEnergy_mixedSector hq hp₂ hw1 hw2 hcert hnormalization]
  have hmain := mixedSector_energy_le hq hp₂ hw1 hw2
  have hM := mixedRawResidualHMinusSq_le_sqrtScale hq ha hp₂ hfive
  have hproj := (lemma_distinct_correction_sigmaEnergy hlambda (by linarith)
    hrhopos.le (by nlinarith [Real.pi_pos]) ha p hp₂).2
  have hsigma := correctionSigmaEnergy_le_sqrtScale hlambda hfive
  have hsqrt : 0 ≤ Real.sqrt (q.scaleLog |p 0|) := Real.sqrt_nonneg _
  have herr : 0 ≤ errorKernelConstant q := (errorKernelConstant_pos hq).le
  nlinarith [hmain, hM, hproj, hsigma, hsqrt, herr]

/-- **The mixed `(h,v)` sector bound of summand 3**, in the shape consumed by
`Manhattan.Glue.summandThreeBound_of_sector_bounds`. -/
theorem summandThreeMixedSectorBound :
    ∃ C₁₂ : ℝ, 0 ≤ C₁₂ ∧
      ∀ q : Estimates.Parameters, q.K = correctedCompetitorK →
          q.rho = correctedCompetitorRho → q.lambda ≤ 1 →
        ∀ (hlambda : 0 < q.lambda) (p : Fin 2 → ℝ), p 0 ∈ Estimates.torus →
          p 1 ∈ Estimates.torus → |p 1| ≤ |p 0| → 0 < |p 0| →
          q.logThreshold < q.scaleLog |p 0| →
        ∀ (hcert : Estimates.LemmaFourTwoIntegralCertificate q (p 0) (p 1))
          (hnormalization : Estimates.degreeOneNormalization q (p 0) ≠ 0),
          (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hlambda
              (Manhattan.type12WalshSynthesis
                (Manhattan.type12WalshAnalysis
                    (walshRaise p (correctedRowVector
                      (correctedLowDegreeData hlambda p hcert hnormalization))) -
                  Manhattan.type112DStarMixed p
                    (correctedLowDegreeData hlambda p hcert
                      hnormalization).mixedCoefficient)) ≤
            C₁₂ * Real.sqrt (q.scaleLog |p 0|) := by
  obtain ⟨C, hCpos, hfiveAll⟩ := exists_propositionFiveTwo_mixed
  refine ⟨(2 * (2 + 2 * (3 / (correctedCompetitorK ^ 3 * correctedCompetitorRho))) + 4) * C,
    ?_, ?_⟩
  · have hK : (0 : ℝ) < correctedCompetitorK := by
      simp [correctedCompetitorK]
    have hrho : (0 : ℝ) < correctedCompetitorRho := by
      simp only [correctedCompetitorRho]
      positivity
    have : (0 : ℝ) ≤ 3 / (correctedCompetitorK ^ 3 * correctedCompetitorRho) := by
      positivity
    nlinarith [hCpos]
  · intro q hK hrho hlam1 hlambda p hp₀ hp₁ horder hpos hlog hcert hnormalization
    have hq : q.Admissible := by
      refine ⟨hlambda, hlam1, ?_, ?_, ?_⟩
      · rw [hK, correctedCompetitorK]
      · rw [hrho, correctedCompetitorRho]
        positivity
      · rw [hrho, correctedCompetitorRho]
    have hqeq : q = ⟨q.lambda, correctedCompetitorK, correctedCompetitorRho⟩ := by
      rw [← hK, ← hrho]
    have hlog' : (⟨q.lambda, correctedCompetitorK, correctedCompetitorRho⟩ :
          Estimates.Parameters).logThreshold <
        (⟨q.lambda, correctedCompetitorK, correctedCompetitorRho⟩ :
          Estimates.Parameters).scaleLog |p 0| := by
      rw [← hqeq]
      exact hlog
    have hfive : Estimates.PropositionFiveTwoIntegralBound 40 C q |p 0| := by
      have h := hfiveAll hlambda hlam1 |p 0| (abs_nonneg _) hlog'
      rw [← hqeq] at h
      exact h
    have herr : errorKernelConstant q =
        3 / (correctedCompetitorK ^ 3 * correctedCompetitorRho) := by
      rw [errorKernelConstant, hK, hrho]
    have hmain := summandThreeMixedSectorBound_of_five hq horder hlog hfive hlambda
      hcert hnormalization
    rwa [herr] at hmain

/-- **Summand 3 of (22) is discharged.** -/
theorem summandThreeBound_proved : ∃ C₃ : ℝ, 0 ≤ C₃ ∧ SummandThreeBound C₃ := by
  obtain ⟨C₁₂, hC₁₂, h12⟩ := summandThreeMixedSectorBound
  have hC₁₁ : 0 ≤ twoRowSummandConstant := by
    obtain ⟨hCpos, -⟩ := Classical.choose_spec exists_twoRowResidual_bound
    rw [twoRowSummandConstant]
    linarith
  exact ⟨2 * twoRowSummandConstant + 2 * C₁₂, by linarith,
    summandThreeBound_of_sector_bounds summandThreeTwoRowSectorBound h12⟩

end

end Manhattan.Glue
