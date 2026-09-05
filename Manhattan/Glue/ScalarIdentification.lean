import Manhattan.Glue.Correction
import Manhattan.Estimates.PropositionFiveTwo

/-!
# Scalar identification for the degree-three correction

This module isolates the scalar part of the calculation in Lemma 5.4. The
two positive pieces `B |v|²` and `σ |v|²` are bounded by the single reduced
integrand `(B + σ)⁻¹` on the support interval. Consequently the final
integral supplied by Proposition 4.2 controls both pieces.

The operator/Fourier intertwining that identifies these scalar forms with
the corresponding Walsh-space quadratic forms is deliberately a separate
interface in `CubicEnergy.lean`.

Paper: `manuscript.tex:1044-1065`, `manuscript.tex:1322-1326`, and
`manuscript.tex:1395-1420`.
-/

open MeasureTheory Set

namespace Manhattan.Glue

noncomputable section

local instance scalarIdentificationPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- The integrand on the right of the reduction estimate (32)--(33). -/
noncomputable def correctionReducedIntegrand (q : Estimates.Parameters)
    (a r beta : ℝ) : ℝ :=
  if r ∈ q.supportInterval a then
    (Estimates.correctionB q r beta +
      Estimates.correctionSigma 40 q a r beta)⁻¹
  else 0

/-- The multiplier-energy integrand `σ |v|²` from (32). -/
noncomputable def correctionSigmaEnergyIntegrand (q : Estimates.Parameters)
    (a r beta : ℝ) : ℝ :=
  Estimates.correctionSigma 40 q a r beta *
    Estimates.correctionV 40 q a r beta ^ 2

/-- The on-support mixed-residual integrand `B |v|²`. -/
noncomputable def correctionBEnergyIntegrand (q : Estimates.Parameters)
    (a r beta : ℝ) : ℝ :=
  Estimates.correctionB q r beta *
    Estimates.correctionV 40 q a r beta ^ 2

/-- The scalar integral remaining on the right of (33). -/
noncomputable def correctionReducedIntegral (q : Estimates.Parameters)
    (a : ℝ) : ℝ :=
  Estimates.torusIntegral fun r : ℝ =>
    Estimates.torusIntegral fun beta : ℝ =>
      correctionReducedIntegrand q a r beta

/-- The scalar multiplier energy in (32), after the disjoint-support
calculation for the two symmetrized summands. -/
noncomputable def correctionSigmaEnergy (q : Estimates.Parameters)
    (a : ℝ) : ℝ :=
  Estimates.torusIntegral fun r : ℝ =>
    Estimates.torusIntegral fun beta : ℝ =>
      correctionSigmaEnergyIntegrand q a r beta

/-- The scalar energy of the desired on-support mixed residual `Bv`. -/
noncomputable def correctionBEnergy (q : Estimates.Parameters)
    (a : ℝ) : ℝ :=
  Estimates.torusIntegral fun r : ℝ =>
    Estimates.torusIntegral fun beta : ℝ =>
      correctionBEnergyIntegrand q a r beta

/-- The `σ` used by the correction is exactly the rank-one quantity from
equation (26), with `η = sin β` and multiplier `M(β,·)`. -/
theorem rankOneSigma_correction (q : Estimates.Parameters)
    (a r beta : ℝ) :
    Estimates.rankOneSigma (Real.sin beta : ℂ)
        (fun alpha : ℝ => Estimates.multiplier 40 q
          (Estimates.mixedTotalFrequency beta alpha))
        (Estimates.correctionInterval q a r beta) =
      Estimates.correctionSigma 40 q a r beta := by
  unfold Estimates.rankOneSigma Estimates.correctionSigma
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

private theorem correctionB_pos {q : Estimates.Parameters}
    (hlambda : 0 < q.lambda) (r beta : ℝ) :
    0 < Estimates.correctionB q r beta := by
  exact Estimates.mixed_denominator_pos hlambda r beta

theorem correctionReducedIntegrand_nonneg {q : Estimates.Parameters}
    (hlambda : 0 < q.lambda) (a r beta : ℝ) :
    0 ≤ correctionReducedIntegrand q a r beta := by
  classical
  by_cases hr : r ∈ q.supportInterval a
  · rw [correctionReducedIntegrand, if_pos hr]
    exact (inv_pos.mpr
      (Estimates.correctionDenominator_pos (by norm_num) hlambda a r beta)).le
  · simp [correctionReducedIntegrand, hr]

theorem correctionSigmaEnergyIntegrand_nonneg {q : Estimates.Parameters}
    (hlambda : 0 < q.lambda) (a r beta : ℝ) :
    0 ≤ correctionSigmaEnergyIntegrand q a r beta := by
  exact mul_nonneg
    (Estimates.correctionSigma_nonneg (by norm_num) hlambda a r beta)
    (sq_nonneg _)

theorem correctionBEnergyIntegrand_nonneg {q : Estimates.Parameters}
    (hlambda : 0 < q.lambda) (a r beta : ℝ) :
    0 ≤ correctionBEnergyIntegrand q a r beta := by
  exact mul_nonneg (correctionB_pos hlambda r beta).le (sq_nonneg _)

/-- Pointwise form of `σ |v|² ≤ (B+σ)⁻¹`. -/
theorem correctionSigmaEnergyIntegrand_le_reduced {q : Estimates.Parameters}
    (hlambda : 0 < q.lambda) (a r beta : ℝ) :
    correctionSigmaEnergyIntegrand q a r beta ≤
      correctionReducedIntegrand q a r beta := by
  classical
  by_cases hr : r ∈ q.supportInterval a
  · let B := Estimates.correctionB q r beta
    let sigma := Estimates.correctionSigma 40 q a r beta
    have hB : 0 < B := correctionB_pos hlambda r beta
    have hsigma : 0 ≤ sigma :=
      Estimates.correctionSigma_nonneg (by norm_num) hlambda a r beta
    have hden : 0 < B + sigma := add_pos_of_pos_of_nonneg hB hsigma
    rw [correctionSigmaEnergyIntegrand, correctionReducedIntegrand,
      Estimates.correctionV, if_pos hr]
    change sigma * (B + sigma)⁻¹ ^ 2 ≤ (B + sigma)⁻¹
    calc
      sigma * (B + sigma)⁻¹ ^ 2 ≤
          (B + sigma) * (B + sigma)⁻¹ ^ 2 := by
        exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
      _ = (B + sigma)⁻¹ := by field_simp
  · simp [correctionSigmaEnergyIntegrand, correctionReducedIntegrand,
      Estimates.correctionV, hr]

/-- Pointwise form of `B |v|² ≤ (B+σ)⁻¹`. -/
theorem correctionBEnergyIntegrand_le_reduced {q : Estimates.Parameters}
    (hlambda : 0 < q.lambda) (a r beta : ℝ) :
    correctionBEnergyIntegrand q a r beta ≤
      correctionReducedIntegrand q a r beta := by
  classical
  by_cases hr : r ∈ q.supportInterval a
  · let B := Estimates.correctionB q r beta
    let sigma := Estimates.correctionSigma 40 q a r beta
    have hB : 0 < B := correctionB_pos hlambda r beta
    have hsigma : 0 ≤ sigma :=
      Estimates.correctionSigma_nonneg (by norm_num) hlambda a r beta
    have hden : 0 < B + sigma := add_pos_of_pos_of_nonneg hB hsigma
    rw [correctionBEnergyIntegrand, correctionReducedIntegrand,
      Estimates.correctionV, if_pos hr]
    change B * (B + sigma)⁻¹ ^ 2 ≤ (B + sigma)⁻¹
    calc
      B * (B + sigma)⁻¹ ^ 2 ≤
          (B + sigma) * (B + sigma)⁻¹ ^ 2 := by
        exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
      _ = (B + sigma)⁻¹ := by field_simp
  · simp [correctionBEnergyIntegrand, correctionReducedIntegrand,
      Estimates.correctionV, hr]

private theorem correctionReducedIntegrand_le_inv {q : Estimates.Parameters}
    (hlambda : 0 < q.lambda) (a r beta : ℝ) :
    correctionReducedIntegrand q a r beta ≤ q.lambda⁻¹ := by
  classical
  by_cases hr : r ∈ q.supportInterval a
  · rw [correctionReducedIntegrand, if_pos hr]
    have hden :=
      Estimates.correctionDenominator_pos (kappa := 40) (q := q)
        (by norm_num) hlambda a r beta
    apply (inv_le_inv₀
      (a := Estimates.correctionB q r beta +
        Estimates.correctionSigma 40 q a r beta)
      (b := q.lambda) hden hlambda).2
    unfold Estimates.correctionB
    linarith [Estimates.dispersion_nonneg r,
      Estimates.dispersion_nonneg beta,
      Estimates.correctionSigma_nonneg (kappa := 40) (q := q)
        (by norm_num) hlambda a r beta]
  · rw [correctionReducedIntegrand, if_neg hr]
    exact inv_nonneg.mpr hlambda.le

private theorem correctionReducedIntegrand_measurable
    (q : Estimates.Parameters) (a : ℝ) :
    Measurable fun z : ℝ × ℝ =>
      correctionReducedIntegrand q a z.1 z.2 := by
  unfold correctionReducedIntegrand
  apply Measurable.ite
  · exact measurableSet_Icc.preimage measurable_fst
  · have hB : Measurable fun z : ℝ × ℝ =>
        Estimates.correctionB q z.1 z.2 := by
      unfold Estimates.correctionB Estimates.dispersion
      fun_prop
    exact (hB.add (Estimates.correctionSigma_measurable 40 q a)).inv
  · exact measurable_const

private theorem correctionSigmaEnergyIntegrand_measurable
    (q : Estimates.Parameters) (a : ℝ) :
    Measurable fun z : ℝ × ℝ =>
      correctionSigmaEnergyIntegrand q a z.1 z.2 := by
  exact (Estimates.correctionSigma_measurable 40 q a).mul
    ((correctionV_measurable 40 q a).pow_const 2)

private theorem correctionBEnergyIntegrand_measurable
    (q : Estimates.Parameters) (a : ℝ) :
    Measurable fun z : ℝ × ℝ =>
      correctionBEnergyIntegrand q a z.1 z.2 := by
  have hB : Measurable fun z : ℝ × ℝ =>
      Estimates.correctionB q z.1 z.2 := by
    unfold Estimates.correctionB Estimates.dispersion
    fun_prop
  exact hB.mul ((correctionV_measurable 40 q a).pow_const 2)

private theorem volume_torus_ne_top :
    volume Estimates.torus ≠ ⊤ := by
  simp [Estimates.torus]

private theorem correctionReducedIntegrable_right {q : Estimates.Parameters}
    (hlambda : 0 < q.lambda) (a r : ℝ) :
    Integrable (fun beta : ℝ => correctionReducedIntegrand q a r beta)
      (volume.restrict Estimates.torus) := by
  apply Integrable.mono'
    (integrableOn_const (C := q.lambda⁻¹) volume_torus_ne_top)
    ((correctionReducedIntegrand_measurable q a).comp
      measurable_prodMk_left).aestronglyMeasurable
  filter_upwards with beta
  change |correctionReducedIntegrand q a r beta| ≤ q.lambda⁻¹
  rw [abs_of_nonneg
    (correctionReducedIntegrand_nonneg hlambda a r beta)]
  exact correctionReducedIntegrand_le_inv hlambda a r beta

private theorem correctionSigmaEnergyIntegrable_right
    {q : Estimates.Parameters} (hlambda : 0 < q.lambda) (a r : ℝ) :
    Integrable (fun beta : ℝ => correctionSigmaEnergyIntegrand q a r beta)
      (volume.restrict Estimates.torus) := by
  apply Integrable.mono'
    (correctionReducedIntegrable_right hlambda a r)
    ((correctionSigmaEnergyIntegrand_measurable q a).comp
      measurable_prodMk_left).aestronglyMeasurable
  filter_upwards with beta
  change |correctionSigmaEnergyIntegrand q a r beta| ≤
    correctionReducedIntegrand q a r beta
  rw [abs_of_nonneg
    (correctionSigmaEnergyIntegrand_nonneg hlambda a r beta)]
  exact correctionSigmaEnergyIntegrand_le_reduced hlambda a r beta

private theorem correctionBEnergyIntegrable_right
    {q : Estimates.Parameters} (hlambda : 0 < q.lambda) (a r : ℝ) :
    Integrable (fun beta : ℝ => correctionBEnergyIntegrand q a r beta)
      (volume.restrict Estimates.torus) := by
  apply Integrable.mono'
    (correctionReducedIntegrable_right hlambda a r)
    ((correctionBEnergyIntegrand_measurable q a).comp
      measurable_prodMk_left).aestronglyMeasurable
  filter_upwards with beta
  change |correctionBEnergyIntegrand q a r beta| ≤
    correctionReducedIntegrand q a r beta
  rw [abs_of_nonneg
    (correctionBEnergyIntegrand_nonneg hlambda a r beta)]
  exact correctionBEnergyIntegrand_le_reduced hlambda a r beta

private theorem torusIntegral_mono_nonneg {f g : ℝ → ℝ}
    (hf : ∀ x, 0 ≤ f x)
    (hg : Integrable g (volume.restrict Estimates.torus))
    (hfg : ∀ x, f x ≤ g x) :
    Estimates.torusIntegral f ≤ Estimates.torusIntegral g := by
  rw [Estimates.torusIntegral, Estimates.torusIntegral]
  simp only [smul_eq_mul]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact integral_mono_of_nonneg
    (Filter.Eventually.of_forall hf) hg (Filter.Eventually.of_forall hfg)

private theorem correctionReducedInner_nonneg {q : Estimates.Parameters}
    (hlambda : 0 < q.lambda) (a r : ℝ) :
    0 ≤ Estimates.torusIntegral fun beta : ℝ =>
      correctionReducedIntegrand q a r beta := by
  unfold Estimates.torusIntegral
  exact mul_nonneg (by positivity)
    (integral_nonneg fun beta =>
      correctionReducedIntegrand_nonneg hlambda a r beta)

private theorem correctionReducedInner_le_inv {q : Estimates.Parameters}
    (hlambda : 0 < q.lambda) (a r : ℝ) :
    (Estimates.torusIntegral fun beta : ℝ =>
      correctionReducedIntegrand q a r beta) ≤ q.lambda⁻¹ := by
  calc
    (Estimates.torusIntegral fun beta : ℝ =>
        correctionReducedIntegrand q a r beta) ≤
        Estimates.torusIntegral (fun _ : ℝ => q.lambda⁻¹) := by
      exact torusIntegral_mono_nonneg
        (fun beta => correctionReducedIntegrand_nonneg hlambda a r beta)
        (integrableOn_const (C := q.lambda⁻¹) volume_torus_ne_top)
        (fun beta => correctionReducedIntegrand_le_inv hlambda a r beta)
    _ = q.lambda⁻¹ := by
      calc
        Estimates.torusIntegral (fun _ : ℝ => q.lambda⁻¹) =
            q.lambda⁻¹ * Estimates.torusIntegral (fun _ : ℝ => (1 : ℝ)) := by
          simp only [Estimates.torusIntegral, smul_eq_mul]
          rw [integral_const, integral_const]
          simp only [smul_eq_mul]
          ring
        _ = q.lambda⁻¹ := by rw [Estimates.torusIntegral_one, mul_one]

private theorem correctionReducedInner_measurable
    (q : Estimates.Parameters) (a : ℝ) :
    Measurable fun r : ℝ => Estimates.torusIntegral fun beta : ℝ =>
      correctionReducedIntegrand q a r beta := by
  unfold Estimates.torusIntegral
  simp only [smul_eq_mul]
  exact (correctionReducedIntegrand_measurable q a).stronglyMeasurable
    |>.integral_prod_right.measurable.const_mul (2 * Real.pi)⁻¹

private theorem correctionSigmaEnergyInner_measurable
    (q : Estimates.Parameters) (a : ℝ) :
    Measurable fun r : ℝ => Estimates.torusIntegral fun beta : ℝ =>
      correctionSigmaEnergyIntegrand q a r beta := by
  unfold Estimates.torusIntegral
  simp only [smul_eq_mul]
  exact (correctionSigmaEnergyIntegrand_measurable q a).stronglyMeasurable
    |>.integral_prod_right.measurable.const_mul (2 * Real.pi)⁻¹

private theorem correctionBEnergyInner_measurable
    (q : Estimates.Parameters) (a : ℝ) :
    Measurable fun r : ℝ => Estimates.torusIntegral fun beta : ℝ =>
      correctionBEnergyIntegrand q a r beta := by
  unfold Estimates.torusIntegral
  simp only [smul_eq_mul]
  exact (correctionBEnergyIntegrand_measurable q a).stronglyMeasurable
    |>.integral_prod_right.measurable.const_mul (2 * Real.pi)⁻¹

private theorem correctionReducedInner_integrable {q : Estimates.Parameters}
    (hlambda : 0 < q.lambda) (a : ℝ) :
    Integrable (fun r : ℝ => Estimates.torusIntegral fun beta : ℝ =>
      correctionReducedIntegrand q a r beta)
      (volume.restrict Estimates.torus) := by
  apply Integrable.mono'
    (integrableOn_const (C := q.lambda⁻¹) volume_torus_ne_top)
    (correctionReducedInner_measurable q a).aestronglyMeasurable
  filter_upwards with r
  rw [Real.norm_eq_abs,
    abs_of_nonneg (correctionReducedInner_nonneg hlambda a r)]
  exact correctionReducedInner_le_inv hlambda a r

private theorem correctionSigmaEnergyInner_le_reduced
    {q : Estimates.Parameters} (hlambda : 0 < q.lambda) (a r : ℝ) :
    (Estimates.torusIntegral fun beta : ℝ =>
      correctionSigmaEnergyIntegrand q a r beta) ≤
      Estimates.torusIntegral fun beta : ℝ =>
        correctionReducedIntegrand q a r beta := by
  exact torusIntegral_mono_nonneg
    (fun beta => correctionSigmaEnergyIntegrand_nonneg hlambda a r beta)
    (correctionReducedIntegrable_right hlambda a r)
    (fun beta => correctionSigmaEnergyIntegrand_le_reduced hlambda a r beta)

private theorem correctionBEnergyInner_le_reduced
    {q : Estimates.Parameters} (hlambda : 0 < q.lambda) (a r : ℝ) :
    (Estimates.torusIntegral fun beta : ℝ =>
      correctionBEnergyIntegrand q a r beta) ≤
      Estimates.torusIntegral fun beta : ℝ =>
        correctionReducedIntegrand q a r beta := by
  exact torusIntegral_mono_nonneg
    (fun beta => correctionBEnergyIntegrand_nonneg hlambda a r beta)
    (correctionReducedIntegrable_right hlambda a r)
    (fun beta => correctionBEnergyIntegrand_le_reduced hlambda a r beta)

private theorem correctionSigmaEnergyInner_nonneg {q : Estimates.Parameters}
    (hlambda : 0 < q.lambda) (a r : ℝ) :
    0 ≤ Estimates.torusIntegral fun beta : ℝ =>
      correctionSigmaEnergyIntegrand q a r beta := by
  unfold Estimates.torusIntegral
  exact mul_nonneg (by positivity)
    (integral_nonneg fun beta =>
      correctionSigmaEnergyIntegrand_nonneg hlambda a r beta)

private theorem correctionBEnergyInner_nonneg {q : Estimates.Parameters}
    (hlambda : 0 < q.lambda) (a r : ℝ) :
    0 ≤ Estimates.torusIntegral fun beta : ℝ =>
      correctionBEnergyIntegrand q a r beta := by
  unfold Estimates.torusIntegral
  exact mul_nonneg (by positivity)
    (integral_nonneg fun beta =>
      correctionBEnergyIntegrand_nonneg hlambda a r beta)

private theorem correctionSigmaEnergyInner_integrable
    {q : Estimates.Parameters} (hlambda : 0 < q.lambda) (a : ℝ) :
    Integrable (fun r : ℝ => Estimates.torusIntegral fun beta : ℝ =>
      correctionSigmaEnergyIntegrand q a r beta)
      (volume.restrict Estimates.torus) := by
  apply Integrable.mono'
    (correctionReducedInner_integrable hlambda a)
    (correctionSigmaEnergyInner_measurable q a).aestronglyMeasurable
  filter_upwards with r
  rw [Real.norm_eq_abs,
    abs_of_nonneg (correctionSigmaEnergyInner_nonneg hlambda a r)]
  exact correctionSigmaEnergyInner_le_reduced hlambda a r

private theorem correctionBEnergyInner_integrable
    {q : Estimates.Parameters} (hlambda : 0 < q.lambda) (a : ℝ) :
    Integrable (fun r : ℝ => Estimates.torusIntegral fun beta : ℝ =>
      correctionBEnergyIntegrand q a r beta)
      (volume.restrict Estimates.torus) := by
  apply Integrable.mono'
    (correctionReducedInner_integrable hlambda a)
    (correctionBEnergyInner_measurable q a).aestronglyMeasurable
  filter_upwards with r
  rw [Real.norm_eq_abs,
    abs_of_nonneg (correctionBEnergyInner_nonneg hlambda a r)]
  exact correctionBEnergyInner_le_reduced hlambda a r

/-- Equation (32) contributes at most the single reduced scalar integral. -/
theorem correctionSigmaEnergy_le_reducedIntegral {q : Estimates.Parameters}
    (hlambda : 0 < q.lambda) (a : ℝ) :
    correctionSigmaEnergy q a ≤ correctionReducedIntegral q a := by
  exact torusIntegral_mono_nonneg
    (fun r => correctionSigmaEnergyInner_nonneg hlambda a r)
    (correctionReducedInner_integrable hlambda a)
    (fun r => correctionSigmaEnergyInner_le_reduced hlambda a r)

/-- The desired on-support mixed residual also contributes at most the
single reduced scalar integral. -/
theorem correctionBEnergy_le_reducedIntegral {q : Estimates.Parameters}
    (hlambda : 0 < q.lambda) (a : ℝ) :
    correctionBEnergy q a ≤ correctionReducedIntegral q a := by
  exact torusIntegral_mono_nonneg
    (fun r => correctionBEnergyInner_nonneg hlambda a r)
    (correctionReducedInner_integrable hlambda a)
    (fun r => correctionBEnergyInner_le_reduced hlambda a r)

theorem correctionReducedIntegral_eq_propositionFiveTwo
    (q : Estimates.Parameters) (a : ℝ) :
    correctionReducedIntegral q a =
      Estimates.torusIntegral (fun r : ℝ =>
        if r ∈ q.supportInterval a then
          Estimates.torusIntegral (fun beta : ℝ =>
            (Estimates.correctionB q r beta +
              Estimates.correctionSigma 40 q a r beta)⁻¹)
        else 0) := by
  classical
  unfold correctionReducedIntegral correctionReducedIntegrand
  congr 1
  funext r
  by_cases hr : r ∈ q.supportInterval a
  · simp only [hr, if_true]
  · simp only [hr, if_false]
    simp [Estimates.torusIntegral]

/-- Proposition 4.2 bounds the scalar multiplier energy by `C √L`. -/
theorem correctionSigmaEnergy_le_sqrtScale {q : Estimates.Parameters}
    (hlambda : 0 < q.lambda) {C a : ℝ}
    (hfive : Estimates.PropositionFiveTwoIntegralBound 40 C q a) :
    correctionSigmaEnergy q a ≤ C * Real.sqrt (q.scaleLog a) := by
  exact (correctionSigmaEnergy_le_reducedIntegral hlambda a).trans <| by
    rw [correctionReducedIntegral_eq_propositionFiveTwo]
    exact hfive

/-- Proposition 4.2 gives the same `C √L` control of the on-support mixed
residual. -/
theorem correctionBEnergy_le_sqrtScale {q : Estimates.Parameters}
    (hlambda : 0 < q.lambda) {C a : ℝ}
    (hfive : Estimates.PropositionFiveTwoIntegralBound 40 C q a) :
    correctionBEnergy q a ≤ C * Real.sqrt (q.scaleLog a) := by
  exact (correctionBEnergy_le_reducedIntegral hlambda a).trans <| by
    rw [correctionReducedIntegral_eq_propositionFiveTwo]
    exact hfive

/-- The two scalar pieces used in the cubic and desired mixed-residual
energies are jointly bounded by `2 C √L`. -/
theorem correctionScalarEnergy_le_sqrtScale {q : Estimates.Parameters}
    (hlambda : 0 < q.lambda) {C a : ℝ}
    (hfive : Estimates.PropositionFiveTwoIntegralBound 40 C q a) :
    correctionSigmaEnergy q a + correctionBEnergy q a ≤
      2 * C * Real.sqrt (q.scaleLog a) := by
  have hsigma := correctionSigmaEnergy_le_sqrtScale hlambda hfive
  have hB := correctionBEnergy_le_sqrtScale hlambda hfive
  linarith

/-- `-- INTERFACE (still open)`: the complete lowering/projection calculation
identifies the concrete mixed-residual energy with the two scalar pieces
isolated in this file. The energy is a parameter so the lowering module can
instantiate its concrete degree-two form without an import cycle.

Status of the three thirds of Lemma 5.4 that feed it:

* Step 2's `L²` form of (D2a)/(D2b) is proved on the whole type-`(1,1,2)`
  sector by `Manhattan.Glue.type112DStarTwoRow_eq` and
  `Manhattan.Glue.type112DStarMixed_eq`
  (`Manhattan/Glue/LoweringClosure.lean`, the formalization);
* Step 3's error term is proved by
  `Manhattan.Estimates.errorHMinusSq_le_rowOrder`
  (`Manhattan/Estimates/KernelBoundError.lean`, the formalization), whose right-hand
  side is `Manhattan.Glue.correctionSigmaEnergy` definitionally;
* the projection-error third is discharged for the actual competitor by module
  A8's `Manhattan.Glue.lemma_distinct_correction` and
  `Manhattan.Glue.lemma_distinct_correction_sigmaEnergy`
  (`Manhattan/Glue/CorrectionLowering.lean`), which carry no diagonal-freeness
  hypothesis and whose instantiating data are certified to be the competitor's
  own Walsh coefficients by
  `Manhattan.Glue.concreteLoweringFormula_correction_certified` (cite that
  PACKAGED theorem: the bare instance
  `Manhattan.Glue.concreteLoweringFormula_correction` discharges its mixed
  clause definitionally, because the mixed datum is *defined* as
  `rawD2StarMixed (rawOffDiagonalPart …)`, so it must not be cited alone; the
  content is `Manhattan.Glue.mixedFourierCoefficient_correction`). The scalar
  right-hand side is evaluateds
  `Manhattan.Glue.projectionErrorHMinusSq_correction_le_two_correctionSigmaEnergy`.
  `Manhattan.Glue.lemma_distinct_shiftedRawCoefficient` is NOT one of these:
  it assumes a diagonal-free kernel and is vacuous as a rendering of Lemma 5.3
  .

Steps 2--4 themselves are now proved on the frequency side, in
`Manhattan/Glue/SummandThree.lean`: `rawD2StarTwoRow_correctionCoefficient`
(no two-row component), `rawD2StarMixed_correction_eq` (the mixed component
is `σv + U`), `mixedRawResidual_eq` (equation `(onI)`), and
`mixedRawResidualHMinusSq_le_reducedIntegral` (equation `(reduce)`), and the
degree-two transport that the paragraph below used to call for is
`Manhattan.Glue.hMinusEnergy_type12WalshSynthesis_torusIntegral`.

What is still missing is the identification of the degree-two Walsh
coefficients of the concrete residual `D₁f_p - D₂*k_p` with those
frequency-side functions, together with the frequency shift of `eq:shift`
recorded in the docstring of `Manhattan/Glue/FinalDischarge.lean`. Note also
that the bound below has no universal constant, whereas
`manuscript.tex:1409-1418` produces `‖·‖²_{-1} ≤ ∫∫(B+σ)⁻¹ + C∫∫σ|v|²`; a
consumer needing the constant should use
`Manhattan.Glue.mixedRawResidualHMinusSq_le_reducedIntegral`, or bound the
concrete summand directly against `Manhattan.Glue.SummandThreeBound`, instead
of routing through this `Prop`. -/
def MixedResidualScalarIdentification (q : Estimates.Parameters) (a : ℝ)
    (mixedResidualEnergy : ℝ) : Prop :=
  mixedResidualEnergy ≤ correctionSigmaEnergy q a + correctionBEnergy q a

/-- Any concrete mixed residual satisfying the explicit identification
interface inherits Proposition 4.2's `2 C √L` bound. -/
theorem mixedResidualEnergy_le_sqrtScale {q : Estimates.Parameters}
    (hlambda : 0 < q.lambda) {C a mixedResidualEnergy : ℝ}
    (hidentify : MixedResidualScalarIdentification q a mixedResidualEnergy)
    (hfive : Estimates.PropositionFiveTwoIntegralBound 40 C q a) :
    mixedResidualEnergy ≤ 2 * C * Real.sqrt (q.scaleLog a) :=
  hidentify.trans (correctionScalarEnergy_le_sqrtScale hlambda hfive)

end

end Manhattan.Glue
