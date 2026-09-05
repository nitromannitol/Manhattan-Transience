import Manhattan.Glue.CubicDischarge
import Manhattan.Glue.ProjectionDischarge

/-!
# Consequences of the multiplier identity for Lemma 5.3 and the competitor

The identity `rawCubicMultiplierEnergy = 2 correctionSigmaEnergy` turns the
right-hand side of Lemma 5.3 into a Proposition 4.2 quantity, and it
specializes to the parameters of the corrected competitor.

Paper: `manuscript.tex:1208-1219`, `manuscript.tex:1274-1303`.
-/

open MeasureTheory Set

namespace Manhattan.Glue

noncomputable section

/-! ### Lemma 5.3 with the raw energy identified -/

/-- Lemma 5.3 with the raw multiplier energy identified: the projection error
is bounded by twice the scalar energy of (30). -/
theorem projectionErrorHMinusSq_le_two_correctionSigmaEnergy
    {q : Estimates.Parameters} (hlambda : 0 < q.lambda) (hK : 1 ≤ q.K)
    (hrho : 0 ≤ q.rho) (hrhopi : 3 * q.rho < Real.pi)
    {a p₂ : ℝ} (ha : 0 ≤ a) (hp₂ : |p₂| ≤ a) (ell : ℝ → ℝ → ℂ)
    (hfinite : ProjectionErrorIntegrable 40 q ell)
    (hraw : RawProjectionEnergyBound q ell (rawCubicMultiplierEnergy q a p₂)) :
    projectionErrorHMinusSq q ell ≤ 2 * correctionSigmaEnergy q a := by
  refine (projectionErrorHMinusSq_le_rawMultiplierEnergy hlambda ell _
    hfinite hraw).trans ?_
  exact le_of_eq (rawCubicMultiplierEnergy_eq_two_correctionSigmaEnergy
    hlambda hK hrho hrhopi ha hp₂)

/-- Consequently the projection error obeys the `√L` bound of Proposition
4.2. -/
theorem projectionErrorHMinusSq_le_sqrtScale
    {q : Estimates.Parameters} (hlambda : 0 < q.lambda) (hK : 1 ≤ q.K)
    (hrho : 0 ≤ q.rho) (hrhopi : 3 * q.rho < Real.pi)
    {C a p₂ : ℝ} (ha : 0 ≤ a) (hp₂ : |p₂| ≤ a) (ell : ℝ → ℝ → ℂ)
    (hfinite : ProjectionErrorIntegrable 40 q ell)
    (hraw : RawProjectionEnergyBound q ell (rawCubicMultiplierEnergy q a p₂))
    (hfive : Estimates.PropositionFiveTwoIntegralBound 40 C q a) :
    projectionErrorHMinusSq q ell ≤ 2 * C * Real.sqrt (q.scaleLog a) := by
  refine (projectionErrorHMinusSq_le_two_correctionSigmaEnergy hlambda hK hrho
    hrhopi ha hp₂ ell hfinite hraw).trans ?_
  have h := correctionSigmaEnergy_le_sqrtScale hlambda hfive
  nlinarith [Real.sqrt_nonneg (q.scaleLog a)]


/-! ### Equation (30) in the shifted frequency variables of Lemma 5.3 -/

theorem torusIntegral_congr_on {f g : ℝ → ℝ}
    (h : ∀ x ∈ Estimates.torus, f x = g x) :
    Estimates.torusIntegral f = Estimates.torusIntegral g := by
  unfold Estimates.torusIntegral
  congr 1
  refine setIntegral_congr_fun ?_ h
  rw [Estimates.torus]
  exact measurableSet_Ioc

/-- Periodizing the second row frequency does not change the raw multiplier
energy, because the inner integral runs over the fundamental domain. -/
theorem rawMultiplierEnergy_periodizeRow (kappa : ℝ)
    (q : Estimates.Parameters) (p₂ : ℝ) (k : ℝ → ℝ → ℝ → ℂ) :
    rawMultiplierEnergy kappa q p₂ (periodizeRow k) =
      rawMultiplierEnergy kappa q p₂ k := by
  unfold rawMultiplierEnergy
  congr 1
  funext beta
  congr 1
  funext r
  refine torusIntegral_congr_on (fun r' hr' => ?_)
  rw [periodizeRow_eq hr']

theorem torusBounded₃_correctionCoefficient {kappa : ℝ}
    {q : Estimates.Parameters} (hkappa : 0 < kappa) (hlambda : 0 < q.lambda)
    (a p₂ : ℝ) :
    TorusBoundedThree (Estimates.correctionCoefficient kappa q a p₂) :=
  ⟨correctionCoefficient_measurable kappa q a p₂,
    ⟨(kappa * q.lambda)⁻¹ * (2 * q.lambda⁻¹),
      fun r r' beta =>
        correctionCoefficient_norm_bound hkappa hlambda a p₂ r r' beta⟩⟩

set_option maxHeartbeats 1000000 in
/-- Equation (30) in the shifted frequency variables used by Lemma 5.3. -/
theorem rawMultiplierEnergy_correctionCoefficient
    {q : Estimates.Parameters} (hlambda : 0 < q.lambda) (hK : 1 ≤ q.K)
    (hrho : 0 ≤ q.rho) (hrhopi : 3 * q.rho < Real.pi)
    {a p₂ : ℝ} (ha : 0 ≤ a) (hp₂ : |p₂| ≤ a) :
    rawMultiplierEnergy 40 q p₂ (Estimates.correctionCoefficient 40 q a p₂) =
      2 * correctionSigmaEnergy q a := by
  have hkappa : (0:ℝ) < 40 := by norm_num
  have hbound : ∀ r r' b : ℝ,
      |cubicSplitDensity 40 q a p₂ r r' b| ≤
        q.lambda⁻¹ ^ 2 * ((40:ℝ) * q.lambda)⁻¹ :=
    fun r r' b => abs_cubicSplitDensity_le hkappa hlambda a p₂ r r' b
  have hinnerBound : ∀ r r' : ℝ,
      |Estimates.torusIntegral fun b => cubicSplitDensity 40 q a p₂ r r' b| ≤
        q.lambda⁻¹ ^ 2 * ((40:ℝ) * q.lambda)⁻¹ :=
    fun r r' => abs_torusIntegral_le (fun b => hbound r r' b)
  -- pointwise splitting of the integrand
  have hpt : ∀ beta r r' : ℝ,
      Estimates.multiplier 40 q
          (Estimates.mixedTotalFrequency beta (mixedAlpha p₂ r r')) *
          ‖Estimates.correctionCoefficient 40 q a p₂ r r' beta‖ ^ 2 =
        cubicSplitDensity 40 q a p₂ r r' beta +
          cubicSplitDensity 40 q a p₂ r' r beta := fun beta r r' =>
    multiplier_mul_norm_correctionCoefficient_sq hkappa hlambda hK ha hp₂ r r' beta
  -- the inner double integral, for a fixed column frequency
  have hslice : ∀ beta : ℝ,
      (Estimates.torusIntegral fun r => Estimates.torusIntegral fun r' =>
          Estimates.multiplier 40 q
              (Estimates.mixedTotalFrequency beta (mixedAlpha p₂ r r')) *
            ‖Estimates.correctionCoefficient 40 q a p₂ r r' beta‖ ^ 2)
        = 2 * Estimates.torusIntegral fun r =>
            Estimates.correctionSigma 40 q a r beta *
              Estimates.correctionV 40 q a r beta ^ 2 := by
    intro beta
    have hin : ∀ r : ℝ,
        (Estimates.torusIntegral fun r' =>
            Estimates.multiplier 40 q
                (Estimates.mixedTotalFrequency beta (mixedAlpha p₂ r r')) *
              ‖Estimates.correctionCoefficient 40 q a p₂ r r' beta‖ ^ 2)
          = (Estimates.torusIntegral fun r' =>
                cubicSplitDensity 40 q a p₂ r r' beta) +
            (Estimates.torusIntegral fun r' =>
                cubicSplitDensity 40 q a p₂ r' r beta) := by
      intro r
      have hcongr : (fun r' : ℝ =>
          Estimates.multiplier 40 q
              (Estimates.mixedTotalFrequency beta (mixedAlpha p₂ r r')) *
            ‖Estimates.correctionCoefficient 40 q a p₂ r r' beta‖ ^ 2)
          = fun r' : ℝ => cubicSplitDensity 40 q a p₂ r r' beta +
              cubicSplitDensity 40 q a p₂ r' r beta := by
        funext r'
        exact hpt beta r r'
      rw [hcongr]
      exact cubicTorusIntegral_add
        (integrable_of_bound
          (cubicSplitDensity_measurable_rowSecond 40 q a p₂ r beta) (C := _)
          (fun r' => hbound r r' beta))
        (integrable_of_bound
          (cubicSplitDensity_measurable_rowFirst 40 q a p₂ r beta) (C := _)
          (fun r' => hbound r' r beta))
    have hcongr2 : (fun r : ℝ => Estimates.torusIntegral fun r' =>
          Estimates.multiplier 40 q
              (Estimates.mixedTotalFrequency beta (mixedAlpha p₂ r r')) *
            ‖Estimates.correctionCoefficient 40 q a p₂ r r' beta‖ ^ 2)
        = fun r : ℝ =>
            (Estimates.torusIntegral fun r' =>
                cubicSplitDensity 40 q a p₂ r r' beta) +
              (Estimates.torusIntegral fun r' =>
                cubicSplitDensity 40 q a p₂ r' r beta) := by
      funext r
      exact hin r
    rw [hcongr2]
    rw [cubicTorusIntegral_add
      (integrable_of_bound (cubicSplitDensity_innerRow_measurable 40 q a p₂ beta)
        (C := _) (fun r => abs_torusIntegral_le (fun r' => hbound r r' beta)))
      (integrable_of_bound
        (cubicSplitDensity_innerRowSwap_measurable 40 q a p₂ beta)
        (C := _) (fun r => abs_torusIntegral_le (fun r' => hbound r' r beta)))]
    have hswapInner : (Estimates.torusIntegral fun r =>
        Estimates.torusIntegral fun r' =>
          cubicSplitDensity 40 q a p₂ r' r beta)
        = (Estimates.torusIntegral fun r =>
            Estimates.torusIntegral fun r' =>
              cubicSplitDensity 40 q a p₂ r r' beta) :=
      cubicTorusIntegral_swap
        (fun x y => cubicSplitDensity 40 q a p₂ y x beta)
        (integrable_of_bound
          (cubicSplitDensity_measurable_rowPairSwap 40 q a p₂ beta)
          (C := _) (fun z => hbound z.2 z.1 beta))
    rw [hswapInner]
    have hfirst : (fun r : ℝ => Estimates.torusIntegral fun r' =>
          cubicSplitDensity 40 q a p₂ r r' beta)
        = fun r : ℝ => Estimates.correctionSigma 40 q a r beta *
            Estimates.correctionV 40 q a r beta ^ 2 := by
      funext r
      exact cubicSplitDensity_integral_r' hlambda hK hrho hrhopi ha hp₂ r beta
    rw [hfirst]
    ring
  have hsigmaMeas : Measurable fun w : ℝ × ℝ =>
      Estimates.correctionSigma 40 q a w.2 w.1 *
        Estimates.correctionV 40 q a w.2 w.1 ^ 2 := by
    have h1 : Measurable fun w : ℝ × ℝ =>
        Estimates.correctionSigma 40 q a w.2 w.1 := by
      have hcomp : (fun w : ℝ × ℝ => Estimates.correctionSigma 40 q a w.2 w.1)
          = (fun z : ℝ × ℝ => Estimates.correctionSigma 40 q a z.1 z.2) ∘
            (fun w : ℝ × ℝ => (w.2, w.1)) := rfl
      rw [hcomp]
      exact (Estimates.correctionSigma_measurable 40 q a).comp
        (measurable_snd.prodMk measurable_fst)
    have h2 : Measurable fun w : ℝ × ℝ =>
        Estimates.correctionV 40 q a w.2 w.1 := by
      have hcomp : (fun w : ℝ × ℝ => Estimates.correctionV 40 q a w.2 w.1)
          = (fun z : ℝ × ℝ => Estimates.correctionV 40 q a z.1 z.2) ∘
            (fun w : ℝ × ℝ => (w.2, w.1)) := rfl
      rw [hcomp]
      exact (correctionV_measurable 40 q a).comp
        (measurable_snd.prodMk measurable_fst)
    exact h1.mul (h2.pow_const 2)
  have hsigmaBound : ∀ r beta : ℝ,
      |Estimates.correctionSigma 40 q a r beta *
        Estimates.correctionV 40 q a r beta ^ 2| ≤
        q.lambda⁻¹ ^ 2 * ((40:ℝ) * q.lambda)⁻¹ := by
    intro r beta
    rw [← cubicSplitDensity_integral_r' hlambda hK hrho hrhopi ha hp₂ r beta]
    exact abs_torusIntegral_le (fun r' => hbound r r' beta)
  unfold rawMultiplierEnergy
  have hcongr3 : (fun beta : ℝ =>
      Estimates.torusIntegral fun r => Estimates.torusIntegral fun r' =>
        Estimates.multiplier 40 q
            (Estimates.mixedTotalFrequency beta (mixedAlpha p₂ r r')) *
          ‖Estimates.correctionCoefficient 40 q a p₂ r r' beta‖ ^ 2)
      = fun beta : ℝ => 2 * Estimates.torusIntegral fun r =>
          Estimates.correctionSigma 40 q a r beta *
            Estimates.correctionV 40 q a r beta ^ 2 := funext hslice
  rw [hcongr3, cubicTorusIntegral_const_mul, correctionSigmaEnergy_eq_double]
  congr 1
  exact cubicTorusIntegral_swap
    (fun beta r => Estimates.correctionSigma 40 q a r beta *
      Estimates.correctionV 40 q a r beta ^ 2)
    (integrable_of_bound hsigmaMeas (C := _)
      (fun w => hsigmaBound w.2 w.1))


/-- **The scalar right-hand side of Lemma 5.3, evaluated for the correction.**
The squared `H⁻¹` norm of the coincident-row projection error of the paper's raw
type-`112` coefficient is at most twice the scalar energy of (30).

This is NOT Lemma 5.3 for the actual correction: the object bounded here lives
entirely on the frequency side, and this statement alone does not prove it equal
to `‖Π₂ D̃₂* k̃ - D₂* k‖²_{H⁻¹}` for that `k̃` (the audit action 2, confirmed by
the audit). Lemma 5.3 for the competitor is the formalizations
`Manhattan.Glue.lemma_distinct_correction` and
`Manhattan.Glue.lemma_distinct_correction_sigmaEnergy`
(`Manhattan/Glue/CorrectionLowering.lean`), which supply both clauses with no
diagonal-freeness hypothesis; the identification of the instantiating data with
the competitor's own Walsh coefficients is
`Manhattan.Glue.concreteLoweringFormula_correction_certified`. Cite that
PACKAGED theorem: the bare instance
`Manhattan.Glue.concreteLoweringFormula_correction` discharges its mixed clause
definitionally and must not be cited alone, the content being
`Manhattan.Glue.mixedFourierCoefficient_correction`. The qualitative clause is
also covered independently by `Manhattan.Glue.type112DStarTwoRow_correction`. -/
theorem projectionErrorHMinusSq_correction_le_two_correctionSigmaEnergy
    {q : Estimates.Parameters} (hlambda : 0 < q.lambda) (hK : 1 ≤ q.K)
    (hrho : 0 ≤ q.rho) (hrhopi : 3 * q.rho < Real.pi)
    {a p₂ : ℝ} (ha : 0 ≤ a) (hp₂ : |p₂| ≤ a) :
    projectionErrorHMinusSq q
        (rawDiagonalPart p₂
          (periodizeRow (Estimates.correctionCoefficient 40 q a p₂))) ≤
      2 * correctionSigmaEnergy q a := by
  have h := projectionErrorHMinusSq_le_rawMultiplierEnergy_unconditional
    (q := q) (p₂ := p₂)
    (k := periodizeRow (Estimates.correctionCoefficient 40 q a p₂)) hlambda
    (torusBounded₃_periodizeRow
      (torusBounded₃_correctionCoefficient (by norm_num) hlambda a p₂))
    (periodizeRow_periodic _)
  rw [rawMultiplierEnergy_periodizeRow] at h
  exact h.trans (le_of_eq (rawMultiplierEnergy_correctionCoefficient
    hlambda hK hrho hrhopi ha hp₂))

/-- Proposition 4.2 bounds the projection error of the actual correction. -/
theorem projectionErrorHMinusSq_correction_le_sqrtScale
    {q : Estimates.Parameters} (hlambda : 0 < q.lambda) (hK : 1 ≤ q.K)
    (hrho : 0 ≤ q.rho) (hrhopi : 3 * q.rho < Real.pi)
    {C a p₂ : ℝ} (ha : 0 ≤ a) (hp₂ : |p₂| ≤ a)
    (hfive : Estimates.PropositionFiveTwoIntegralBound 40 C q a) :
    projectionErrorHMinusSq q
        (rawDiagonalPart p₂
          (periodizeRow (Estimates.correctionCoefficient 40 q a p₂))) ≤
      2 * C * Real.sqrt (q.scaleLog a) := by
  refine (projectionErrorHMinusSq_correction_le_two_correctionSigmaEnergy
    hlambda hK hrho hrhopi ha hp₂).trans ?_
  have h := correctionSigmaEnergy_le_sqrtScale hlambda hfive
  nlinarith [Real.sqrt_nonneg (q.scaleLog a)]

/-! ### Specialization to the corrected competitor -/

theorem correctedCompetitorK_one_le : (1:ℝ) ≤ correctedCompetitorK := by
  rw [correctedCompetitorK]; norm_num

theorem correctedCompetitorRho_nonneg : (0:ℝ) ≤ correctedCompetitorRho := by
  rw [correctedCompetitorRho]
  positivity

theorem correctedCompetitorRho_three_lt_pi :
    3 * correctedCompetitorRho < Real.pi := by
  rw [correctedCompetitorRho]
  linarith [Real.pi_pos]

/-- Equation (30) for the parameters of the corrected competitor. -/
theorem correctedCompetitor_rawCubicMultiplierEnergy_eq {lambda : ℝ}
    (hlambda : 0 < lambda) {a p₂ : ℝ} (ha : 0 ≤ a) (hp₂ : |p₂| ≤ a) :
    rawCubicMultiplierEnergy
        ⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩ a p₂ =
      2 * correctionSigmaEnergy
        ⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩ a :=
  rawCubicMultiplierEnergy_eq_two_correctionSigmaEnergy
    (q := ⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩)
    hlambda correctedCompetitorK_one_le correctedCompetitorRho_nonneg
    correctedCompetitorRho_three_lt_pi ha hp₂

/-- The `CubicMultiplierScalarIdentification` interface holds for the
corrected competitor's parameters. -/
theorem correctedCompetitor_cubicMultiplierScalarIdentification {lambda : ℝ}
    (hlambda : 0 < lambda) {a p₂ : ℝ} (ha : 0 ≤ a) (hp₂ : |p₂| ≤ a) :
    CubicMultiplierScalarIdentification
      ⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩ hlambda a p₂
      (fun _ => rawCubicMultiplierEnergy
        ⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩ a p₂) :=
  cubicMultiplierScalarIdentification_rawForm
    (q := ⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩)
    hlambda correctedCompetitorK_one_le correctedCompetitorRho_nonneg
    correctedCompetitorRho_three_lt_pi ha hp₂


/-- Lemma 5.3 for the corrected competitor's parameters. -/
theorem correctedCompetitor_projectionErrorHMinusSq_le {lambda : ℝ}
    (hlambda : 0 < lambda) {a p₂ : ℝ} (ha : 0 ≤ a) (hp₂ : |p₂| ≤ a) :
    projectionErrorHMinusSq
        ⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩
        (rawDiagonalPart p₂
          (periodizeRow (Estimates.correctionCoefficient 40
            ⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩ a p₂))) ≤
      2 * correctionSigmaEnergy
        ⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩ a :=
  projectionErrorHMinusSq_correction_le_two_correctionSigmaEnergy
    (q := ⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩)
    hlambda correctedCompetitorK_one_le correctedCompetitorRho_nonneg
    correctedCompetitorRho_three_lt_pi ha hp₂

end

end Manhattan.Glue
