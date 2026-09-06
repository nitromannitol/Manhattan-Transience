import Manhattan.Estimates.RankOne
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The degree-three correction and Proposition 4.2 vocabulary

All objects are explicit functions of real frequencies. No probability-space
objects occur here.

Paper: `manuscript.tex:1002-1128`, `manuscript.tex:1305-1421`.
-/

open MeasureTheory Set

namespace Manhattan.Estimates

noncomputable section

/-- Classical decidability, local to this file: the statements here are analytic, not computational. -/
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- The interval `J(r,β)` from Step 1 of Proposition 4.2. -/
noncomputable def correctionInterval (q : Parameters) (a r beta : ℝ) : Set ℝ :=
  if r ∈ q.supportInterval a ∧ r + q.delta a + |beta| ≤ q.rho / (8 * q.K) then
    Set.Icc (-q.rho) (-4 * q.K * (r + q.delta a + |beta|))
  else ∅

/-- The mixed `H⁻¹` denominator `B(r,β)` from (30). -/
def correctionB (q : Parameters) (r beta : ℝ) : ℝ :=
  q.lambda + dispersion r + dispersion beta

/-- The logarithmic correction `σ(r,β)` from (31). -/
noncomputable def correctionSigma (kappa : ℝ) (q : Parameters) (a r beta : ℝ) : ℝ :=
  Real.sin beta ^ 2 * torusIntegral (fun alpha : ℝ =>
    if alpha ∈ correctionInterval q a r beta then
      (multiplier kappa q (mixedTotalFrequency beta alpha))⁻¹
    else 0)

/-- The scalar minimizer `v = 1_I/(B+σ)` from (32). -/
noncomputable def correctionV (kappa : ℝ) (q : Parameters) (a r beta : ℝ) : ℝ :=
  if r ∈ q.supportInterval a then
    (correctionB q r beta + correctionSigma kappa q a r beta)⁻¹
  else 0

/-- The symmetric degree-three coefficient (without any tuple projection).
The actual coefficient is indexed by a three-element Finset, so
distinctness is part of its type. This frequency formula records the two
row-frequency contributions that remain after that bookkeeping change.
-/
noncomputable def correctionCoefficient (kappa : ℝ) (q : Parameters)
    (a p₂ r r' beta : ℝ) : ℂ :=
  let alpha := r + r' - p₂
  Complex.I * (Real.sin beta : ℂ) /
    (multiplier kappa q (mixedTotalFrequency beta alpha) : ℂ) *
      ((correctionV kappa q a r beta : ℂ) *
          (if alpha ∈ correctionInterval q a r beta then 1 else 0) +
       (correctionV kappa q a r' beta : ℂ) *
          (if alpha ∈ correctionInterval q a r' beta then 1 else 0))

/-- The target denominator lower bound (33), packaged as a pure pointwise proposition. -/
def DenominatorBound (kappa c : ℝ) (q : Parameters) (a : ℝ) : Prop :=
  ∀ r ∈ q.supportInterval a, ∀ beta ∈ torus,
    c * (q.lambda + r ^ 2 + beta ^ 2 *
      (1 + logPos (q.r0 / (r + |beta|)))) ≤
      correctionB q r beta + correctionSigma kappa q a r beta

/-- The target β-integral bound (34). -/
def BetaIntegralBound (kappa C : ℝ) (q : Parameters) (a : ℝ) : Prop :=
  ∀ r ∈ q.supportInterval a,
    torusIntegral (fun beta : ℝ =>
      (correctionB q r beta + correctionSigma kappa q a r beta)⁻¹) ≤
      C / (r * Real.sqrt (1 + Real.log (q.r0 / r)))

/-- The analytic conclusion of Proposition 4.2 after the coefficient
calculation has reduced it to the `(r,β)` integral. -/
def PropositionFiveTwoIntegralBound (kappa C : ℝ) (q : Parameters) (a : ℝ) : Prop :=
  torusIntegral (fun r : ℝ =>
    if r ∈ q.supportInterval a then
      torusIntegral (fun beta : ℝ =>
        (correctionB q r beta + correctionSigma kappa q a r beta)⁻¹)
    else 0) ≤ C * Real.sqrt (q.scaleLog a)

/-- The Euler identity `(B+σ)v=1` on the support interval. -/
theorem correctionV_euler {kappa : ℝ} {q : Parameters} {a r beta : ℝ}
    (hr : r ∈ q.supportInterval a)
    (hne : correctionB q r beta + correctionSigma kappa q a r beta ≠ 0) :
    (correctionB q r beta + correctionSigma kappa q a r beta) *
      correctionV kappa q a r beta = 1 := by
  simp [correctionV, hr, hne]

/-- The algebraic identity `1-σv=Bv` used in Step 2 of Lemma 5.4. -/
theorem one_sub_sigma_mul_correctionV {kappa : ℝ} {q : Parameters} {a r beta : ℝ}
    (hr : r ∈ q.supportInterval a)
    (hne : correctionB q r beta + correctionSigma kappa q a r beta ≠ 0) :
    1 - correctionSigma kappa q a r beta * correctionV kappa q a r beta =
      correctionB q r beta * correctionV kappa q a r beta := by
  have heuler := correctionV_euler hr hne
  linarith

/-- The correction `σ` is nonnegative for positive `κ` and `λ`. -/
theorem correctionSigma_nonneg {kappa : ℝ} {q : Parameters}
    (hkappa : 0 < kappa) (hlambda : 0 < q.lambda) (a r beta : ℝ) :
    0 ≤ correctionSigma kappa q a r beta := by
  rw [correctionSigma]
  apply mul_nonneg (sq_nonneg _)
  rw [torusIntegral]
  simp only [smul_eq_mul]
  apply mul_nonneg (by positivity)
  apply integral_nonneg_of_ae
  filter_upwards with alpha
  split_ifs
  · exact (inv_pos.2 (multiplier_pos hkappa hlambda _)).le
  · exact le_rfl

/-- Joint measurability of the logarithmic correction.  This is needed to
certify that Proposition 4.2 integrates an honest finite function rather than
using the undefined-integral convention. -/
theorem correctionSigma_measurable (kappa : ℝ) (q : Parameters) (a : ℝ) :
    Measurable (fun z : ℝ × ℝ => correctionSigma kappa q a z.1 z.2) := by
  let F : (ℝ × ℝ) → ℝ → ℝ := fun z alpha =>
    if alpha ∈ correctionInterval q a z.1 z.2 then
      (multiplier kappa q (mixedTotalFrequency z.2 alpha))⁻¹
    else 0
  have hset : MeasurableSet {w : (ℝ × ℝ) × ℝ |
      w.2 ∈ correctionInterval q a w.1.1 w.1.2} := by
    unfold correctionInterval Parameters.supportInterval Parameters.delta Parameters.r0
    simp only [Set.mem_ite_empty_right, Set.mem_Icc]
    measurability
  have hF : Measurable (Function.uncurry F) := by
    apply Measurable.ite hset
    · simp only [multiplier, mixedTotalFrequency, theta, Matrix.cons_val_zero,
        Matrix.cons_val_one, dispersion]
      fun_prop
    · exact measurable_const
  have hinner : StronglyMeasurable (fun z : ℝ × ℝ =>
      ∫ alpha, F z alpha ∂(volume.restrict torus)) :=
    hF.stronglyMeasurable.integral_prod_right
  unfold correctionSigma torusIntegral
  simp only [smul_eq_mul]
  exact (Real.continuous_sin.measurable.comp measurable_snd).pow_const 2 |>.mul
    (hinner.measurable.const_mul (2 * Real.pi)⁻¹)

/-- Measurability in the integrated `beta` variable at fixed `r`. -/
theorem correctionSigma_measurable_right (kappa : ℝ) (q : Parameters) (a r : ℝ) :
    Measurable (fun beta : ℝ => correctionSigma kappa q a r beta) := by
  change Measurable ((fun z : ℝ × ℝ => correctionSigma kappa q a z.1 z.2) ∘
    fun beta : ℝ => (r, beta))
  exact (correctionSigma_measurable kappa q a).comp measurable_prodMk_left

/-- The denominator in (32)--(34) is strictly positive. -/
theorem correctionDenominator_pos {kappa : ℝ} {q : Parameters}
    (hkappa : 0 < kappa) (hlambda : 0 < q.lambda) (a r beta : ℝ) :
    0 < correctionB q r beta + correctionSigma kappa q a r beta := by
  apply add_pos_of_pos_of_nonneg
  · exact mixed_denominator_pos hlambda r beta
  · exact correctionSigma_nonneg hkappa hlambda a r beta

end

end Manhattan.Estimates
