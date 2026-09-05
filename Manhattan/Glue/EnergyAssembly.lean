import Manhattan.Glue.LowLog

/-!
# Assembly of the corrected fixed-frequency competitor

This file combines the horizontal high-logarithmic estimate with the
row/column unitary and the elementary low-logarithmic estimate. The sole
remaining premise is isolated as a named proposition so the W7A/W7B lowering,
projection, cubic-energy, and scalar-identification modules can discharge it
without creating import cycles.

Paper: `manuscript.tex:1134-1165`.
-/

noncomputable section

namespace Manhattan.Glue

/-- The elementary normalization inequality used after (24)--(25). It is
kept separate from the model calculation: Lemma 4.1 supplies `b >= c a L`,
whereas the remaining sector estimates supply a numerator of order
`sqrt L`. -/
theorem inverseNormalization_sq_mul_sqrt_le
    {c M a L b : ℝ} (hc : 0 < c) (hM : 0 ≤ M) (ha : 0 < a)
    (hL : 0 < L) (hb : c * a * L ≤ b) :
    b⁻¹ ^ 2 * (M * Real.sqrt L) ≤
      (M * c⁻¹ ^ 2) * (a ^ 2 * L ^ (3 / 2 : ℝ))⁻¹ := by
  have hcaL : 0 < c * a * L := mul_pos (mul_pos hc ha) hL
  have hbpos : 0 < b := hcaL.trans_le hb
  have hinv : b⁻¹ ≤ (c * a * L)⁻¹ :=
    (inv_le_inv₀ hbpos hcaL).2 hb
  have hinvSq : b⁻¹ ^ 2 ≤ (c * a * L)⁻¹ ^ 2 :=
    (sq_le_sq₀ (inv_nonneg.mpr hbpos.le)
      (inv_nonneg.mpr hcaL.le)).2 hinv
  have hsqrtNonneg : 0 ≤ M * Real.sqrt L :=
    mul_nonneg hM (Real.sqrt_nonneg L)
  refine (mul_le_mul_of_nonneg_right hinvSq hsqrtNonneg).trans_eq ?_
  have hsqrtPos : 0 < Real.sqrt L := Real.sqrt_pos.2 hL
  have hsqrtSq : Real.sqrt L ^ 2 = L := Real.sq_sqrt hL.le
  have hthreeHalves : L ^ (3 / 2 : ℝ) = Real.sqrt L ^ 3 := by
    calc
      L ^ (3 / 2 : ℝ) = Real.sqrt L ^ (3 : ℝ) :=
        Real.rpow_div_two_eq_sqrt 3 hL.le
      _ = Real.sqrt L ^ (3 : ℕ) := Real.rpow_natCast _ 3
  have hsqrtFour : Real.sqrt L ^ 4 = L ^ 2 := by
    calc
      Real.sqrt L ^ 4 = (Real.sqrt L ^ 2) ^ 2 := by ring
      _ = L ^ 2 := by rw [hsqrtSq]
  rw [hthreeHalves]
  field_simp [hc.ne', ha.ne', hsqrtPos.ne']
  rw [hsqrtFour]
  ring

/-- The model-specific remainder after the exact constant cancellation. The
premise is deliberately *unnormalized*, so all uses of Lemma 4.1 and
(24)--(25) remain proved in this assembly file.

discharged in `Glue/Discharge.lean` by
`correctedUnnormalizedEnergyInterface_of_sectorEnergy`, from the paper's
four-sector estimate (23) alone. -/
def CorrectedUnnormalizedEnergyInterface (M : ℝ) : Prop :=
  ∀ {lambda : ℝ}, ∀ hlambda : 0 < lambda,
    lambda ≤ 1 →
    ∀ p : Fin 2 → ℝ,
      p 0 ∈ Manhattan.Estimates.torus →
      p 1 ∈ Manhattan.Estimates.torus →
      |p 1| ≤ |p 0| →
      0 < |p 0| →
      let q : Manhattan.Estimates.Parameters :=
        ⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩
      q.logThreshold < q.scaleLog |p 0| →
      ∀ (hcert : Manhattan.Estimates.LemmaFourTwoIntegralCertificate q
          (p 0) (p 1))
        (hnormalization : Manhattan.Estimates.degreeOneNormalization q
          (p 0) ≠ 0),
        let d := correctedLowDegreeData hlambda p hcert hnormalization
        d.CancelsAt p →
        (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hEnergy
              lambda
              (Manhattan.degreeOneFrequencySynthesis Manhattan.Axis.horizontal
                  d.rowFrequency +
                Manhattan.type112WalshSynthesis d.mixedCoefficient) +
            (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy
              hlambda
              ((d.normalization : ℂ) • Manhattan.walshL2 ∅ -
                Manhattan.concreteFiberA p
                  (Manhattan.degreeOneFrequencySynthesis Manhattan.Axis.horizontal
                      d.rowFrequency +
                    Manhattan.type112WalshSynthesis d.mixedCoefficient)) ≤
          M * Real.sqrt (q.scaleLog |p 0|)

/-- The complete horizontal high-logarithmic conclusion of the lowering,
projection-error, cubic-energy, and scalar-identification calculations. This
is the exact surface requested in the stage report.

discharged in `Glue/Discharge.lean` by
`correctedHorizontalEnergySupply_of_sectorEnergy`. -/
def CorrectedHorizontalEnergyInterface (C : ℝ) : Prop :=
  ∀ {lambda : ℝ}, ∀ hlambda : 0 < lambda,
    lambda ≤ 1 →
    ∀ p : Fin 2 → ℝ,
      p 0 ∈ Manhattan.Estimates.torus →
      p 1 ∈ Manhattan.Estimates.torus →
      |p 1| ≤ |p 0| →
      0 < |p 0| →
      let q : Manhattan.Estimates.Parameters :=
        ⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩
      q.logThreshold < q.scaleLog |p 0| →
      ∃ (hcert : Manhattan.Estimates.LemmaFourTwoIntegralCertificate q
          (p 0) (p 1))
        (hnormalization : Manhattan.Estimates.degreeOneNormalization q
          (p 0) ≠ 0),
        let d := correctedLowDegreeData hlambda p hcert hnormalization
        (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hEnergy
              lambda d.competitor +
            (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy
              hlambda (Manhattan.walshL2 ∅ -
                Manhattan.concreteFiberA p d.competitor) ≤
          C * Manhattan.Operator.correctedMajorant
            correctedCompetitorCutoff lambda p

/-- Lemma 4.1 v3, the exact cancellation (24), and the normalization identity
(25) turn the unnormalized W7A/W7B sector bound into the exact horizontal
high-logarithmic interface. In particular, positivity and the lower bound on
`b_p` are not delegated to the operator layer. -/
theorem correctedHorizontalEnergyInterface_exists_of_unnormalized
    (M : ℝ) (hM : 0 ≤ M)
    (hunnormalized : CorrectedUnnormalizedEnergyInterface M) :
    ∃ C : ℝ, 0 ≤ C ∧ CorrectedHorizontalEnergyInterface C := by
  obtain ⟨c, _, hc, _, hlemma⟩ :=
    Manhattan.Estimates.lemmaFourTwoSuccessorV3Claim_proved
      correctedCompetitorK correctedCompetitorRho
      (by simp [correctedCompetitorK])
      (by simp [correctedCompetitorRho]; positivity)
      (by simp [correctedCompetitorRho])
  refine ⟨M * c⁻¹ ^ 2, mul_nonneg hM (sq_nonneg _), ?_⟩
  intro lambda hlambda hlambdaOne p hp₀ hp₁ horder hpositive
  let q : Manhattan.Estimates.Parameters :=
    ⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩
  change q.logThreshold < q.scaleLog |p 0| → _
  intro hlog
  have hs := hlemma lambda hlambda hlambdaOne (p 0) (p 1)
    hp₀ hp₁ horder hpositive hlog
  have hthresholdPos : 0 < q.logThreshold := by
    simp only [q, Manhattan.Estimates.Parameters.logThreshold,
      correctedCompetitorK]
    have hlogK : 0 < Real.log 20 := Real.log_pos (by norm_num)
    linarith
  have hscalePos : 0 < q.scaleLog |p 0| := hthresholdPos.trans hlog
  have hnormalizationPos :
      0 < Manhattan.Estimates.degreeOneNormalization q (p 0) :=
    (mul_pos (mul_pos hc hpositive) hscalePos).trans_le hs.2.2.1
  let hcert := hs.1
  let hnormalization :
      Manhattan.Estimates.degreeOneNormalization q (p 0) ≠ 0 :=
    hnormalizationPos.ne'
  let d := correctedLowDegreeData hlambda p hcert hnormalization
  have hcancels : d.CancelsAt p := by
    exact correctedLowDegreeData_cancelsAt hlambda p hcert hnormalization hs.2.1
  have hraw := hunnormalized hlambda hlambdaOne p hp₀ hp₁ horder
    hpositive hlog hcert hnormalization hcancels
  have hmax : Manhattan.Operator.maxFrequency p = |p 0| :=
    max_eq_left horder
  have hmaxNe : Manhattan.Operator.maxFrequency p ≠ 0 := by
    rw [hmax]
    exact hpositive.ne'
  have hscale :
      Manhattan.Operator.frequencyLogScale correctedCompetitorCutoff lambda p =
        q.scaleLog |p 0| := by
    calc
      Manhattan.Operator.frequencyLogScale correctedCompetitorCutoff lambda p =
          q.scaleLog (Manhattan.Operator.maxFrequency p) := by
        simpa [q, Manhattan.Estimates.Parameters.r0,
          correctedCompetitorCutoff] using
          (Manhattan.Estimates.operator_frequencyLogScale_eq_scaleLog q p)
      _ = q.scaleLog |p 0| := by rw [hmax]
  have hmajorant :
      Manhattan.Operator.correctedMajorant correctedCompetitorCutoff lambda p =
        (|p 0| ^ 2 * (q.scaleLog |p 0|) ^ (3 / 2 : ℝ))⁻¹ := by
    rw [Manhattan.Operator.correctedMajorant, if_neg hmaxNe, one_div,
      hmax, hscale]
  refine ⟨hcert, hnormalization, ?_⟩
  change
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hEnergy
          lambda d.competitor +
        (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy
          hlambda (Manhattan.walshL2 ∅ -
            Manhattan.concreteFiberA p d.competitor) ≤
      (M * c⁻¹ ^ 2) * Manhattan.Operator.correctedMajorant
        correctedCompetitorCutoff lambda p
  rw [lowDegreeCompetitor_objective_eq_unnormalized d p hlambda
    hnormalizationPos]
  calc
    (Manhattan.Estimates.degreeOneNormalization q (p 0))⁻¹ ^ 2 *
          ((Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hEnergy
                lambda
                (Manhattan.degreeOneFrequencySynthesis Manhattan.Axis.horizontal
                    d.rowFrequency +
                  Manhattan.type112WalshSynthesis d.mixedCoefficient) +
              (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy
                hlambda
                ((d.normalization : ℂ) • Manhattan.walshL2 ∅ -
                  Manhattan.concreteFiberA p
                    (Manhattan.degreeOneFrequencySynthesis Manhattan.Axis.horizontal
                        d.rowFrequency +
                      Manhattan.type112WalshSynthesis d.mixedCoefficient))) ≤
        (Manhattan.Estimates.degreeOneNormalization q (p 0))⁻¹ ^ 2 *
          (M * Real.sqrt (q.scaleLog |p 0|)) :=
      mul_le_mul_of_nonneg_left hraw (sq_nonneg _)
    _ ≤ (M * c⁻¹ ^ 2) *
        (|p 0| ^ 2 * (q.scaleLog |p 0|) ^ (3 / 2 : ℝ))⁻¹ :=
      inverseNormalization_sq_mul_sqrt_le hc hM hpositive hscalePos
        hs.2.2.1
    _ = (M * c⁻¹ ^ 2) *
        Manhattan.Operator.correctedMajorant
          correctedCompetitorCutoff lambda p := by rw [hmajorant]

/-- Conditional form of the exact horizontal theorem while the independent
W7A/W7B files are being joined. -/
theorem correctedLowDegreeData_energy_horizontal_of_interface
    (C : ℝ) (hinterface : CorrectedHorizontalEnergyInterface C)
    {lambda : ℝ} (hlambda : 0 < lambda)
    (hlambdaOne : lambda ≤ 1)
    (p : Fin 2 → ℝ) (hp₀ : p 0 ∈ Manhattan.Estimates.torus)
    (hp₁ : p 1 ∈ Manhattan.Estimates.torus) (horder : |p 1| ≤ |p 0|)
    (hpositive : 0 < |p 0|) :
    let q : Manhattan.Estimates.Parameters :=
      ⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩
    q.logThreshold < q.scaleLog |p 0| →
    ∃ (hcert : Manhattan.Estimates.LemmaFourTwoIntegralCertificate q
          (p 0) (p 1))
      (hnormalization : Manhattan.Estimates.degreeOneNormalization q
          (p 0) ≠ 0),
      let d := correctedLowDegreeData hlambda p hcert hnormalization
      (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hEnergy
            lambda d.competitor +
          (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy
            hlambda (Manhattan.walshL2 ∅ -
              Manhattan.concreteFiberA p d.competitor) ≤
        C * Manhattan.Operator.correctedMajorant
          correctedCompetitorCutoff lambda p := by
  exact hinterface hlambda hlambdaOne p hp₀ hp₁ horder hpositive

theorem correctedMajorant_nonneg {r0 lambda : ℝ} (hlambda : 0 < lambda)
    (p : Fin 2 → ℝ) :
    0 ≤ Manhattan.Operator.correctedMajorant r0 lambda p := by
  by_cases hzero : Manhattan.Operator.maxFrequency p = 0
  · rw [Manhattan.Operator.correctedMajorant, if_pos hzero]
    exact driftlessMajorant_nonneg hlambda p
  · rw [Manhattan.Operator.correctedMajorant, if_neg hzero]
    apply one_div_nonneg.mpr
    apply mul_nonneg (sq_nonneg _)
    exact Real.rpow_nonneg
      (zero_le_one.trans (frequencyLogScale_one_le r0 lambda p)) _

/-- All three frequency regimes give a concrete Walsh competitor, conditional
only on the horizontal high-logarithmic interface. -/
theorem correctedCompetitor_all_frequencies_of_horizontal
    (C : ℝ) (hC : 0 ≤ C)
    (hinterface : CorrectedHorizontalEnergyInterface C) :
    ∀ (lambda : ℝ), ∀ hlambda : 0 < lambda, lambda ≤ 1 →
      ∀ p : Fin 2 → ℝ,
        p 0 ∈ Manhattan.Estimates.torus →
        p 1 ∈ Manhattan.Estimates.torus →
        ∃ g : Manhattan.WalshL2,
          (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hEnergy
                lambda g +
              (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy
                hlambda (Manhattan.walshL2 ∅ -
                  Manhattan.concreteFiberA p g) ≤
            (C + correctedLowLogConstant + 1) *
              Manhattan.Operator.correctedMajorant
                correctedCompetitorCutoff lambda p := by
  intro lambda hlambda hlambdaOne p hp₀ hp₁
  have hmajorant : 0 ≤ Manhattan.Operator.correctedMajorant
      correctedCompetitorCutoff lambda p := correctedMajorant_nonneg hlambda p
  have hCglobal : C ≤ C + correctedLowLogConstant + 1 := by
    nlinarith [correctedLowLogConstant_nonneg]
  have hLowGlobal : correctedLowLogConstant ≤
      C + correctedLowLogConstant + 1 := by
    nlinarith
  by_cases hzero : Manhattan.Operator.maxFrequency p = 0
  · obtain ⟨g, hg⟩ := concrete_driftless_competitor lambda hlambda p
    refine ⟨g, hg.trans ?_⟩
    exact (driftlessMajorant_le_corrected_of_maxFrequency_eq_zero
      hlambda p hzero).trans
        (mul_le_mul_of_nonneg_right hLowGlobal hmajorant)
  · let q : Manhattan.Estimates.Parameters :=
      ⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩
    by_cases hhigh : q.logThreshold <
        q.scaleLog (Manhattan.Operator.maxFrequency p)
    · by_cases horder : |p 1| ≤ |p 0|
      · have hmax : Manhattan.Operator.maxFrequency p = |p 0| := by
          exact max_eq_left horder
        have hp₀pos : 0 < |p 0| := by
          apply abs_pos.mpr
          intro hp
          apply hzero
          rw [hmax, hp, abs_zero]
        have hhigh₀ : q.logThreshold < q.scaleLog |p 0| := by
          rwa [hmax] at hhigh
        obtain ⟨hcert, hnormalization, hbound⟩ :=
          hinterface hlambda hlambdaOne p hp₀ hp₁ horder hp₀pos hhigh₀
        let d := correctedLowDegreeData hlambda p hcert hnormalization
        refine ⟨d.competitor, hbound.trans ?_⟩
        exact mul_le_mul_of_nonneg_right hCglobal hmajorant
      · have horder' : |p 0| ≤ |p 1| := (lt_of_not_ge horder).le
        have hmax : Manhattan.Operator.maxFrequency p = |p 1| :=
          max_eq_right horder'
        have hp₁pos : 0 < |p 1| := by
          apply abs_pos.mpr
          intro hp
          apply hzero
          rw [hmax, hp, abs_zero]
        have hhigh₁ : q.logThreshold < q.scaleLog |p 1| := by
          rwa [hmax] at hhigh
        obtain ⟨hcert, hnormalization, hbound⟩ :=
          hinterface hlambda hlambdaOne (axisSwapFrequency p) hp₁ hp₀
            horder' hp₁pos (by simpa using hhigh₁)
        let d := correctedLowDegreeData hlambda (axisSwapFrequency p)
          hcert hnormalization
        obtain ⟨g, hg⟩ := correctedCompetitor_of_axisSwap hlambda p
          ⟨d.competitor, hbound⟩
        refine ⟨g, hg.trans ?_⟩
        exact mul_le_mul_of_nonneg_right hCglobal hmajorant
    · have hlow : q.scaleLog (Manhattan.Operator.maxFrequency p) ≤
          q.logThreshold := le_of_not_gt hhigh
      refine ⟨zeroLowDegreeCompetitorData.competitor, ?_⟩
      exact (correctedLowDegreeData_energy_lowLog hlambda p hp₀ hp₁ hlow).trans
        (mul_le_mul_of_nonneg_right hLowGlobal hmajorant)

end Manhattan.Glue
