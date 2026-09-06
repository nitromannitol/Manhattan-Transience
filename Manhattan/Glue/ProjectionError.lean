import Manhattan.Glue.Lowering
import Manhattan.Estimates.LineResolvent
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# The type-112 diagonal projection error

This file isolates the analytic estimate in Lemma 5.3.  In the Finset
encoding, the discarded coincident-row part is represented by a function
`ell(alpha,beta)`.  Removing the column sign is killed by the degree-two
Finset projection; removing a row leaves the single mixed component below.

All integrals are normalized Haar integrals on the paper's real torus.

Paper: `manuscript.tex:1208-1219`, `manuscript.tex:1274-1303`, and
`manuscript.tex:1402-1417`.
-/

open MeasureTheory Set

namespace Manhattan.Glue

noncomputable section

/-- The mixed component left by the coincident-row projection error.  The
Finset normalization has coefficient one (not the tuple-space `sqrt 2`). -/
noncomputable def projectionMixedError (ell : ℝ → ℝ → ℂ)
    (beta : ℝ) : ℂ :=
  -Complex.I * (Real.sin beta : ℂ) *
    Estimates.torusIntegral (fun alpha => ell alpha beta)

/-- The squared `H⁻¹` norm of the projection error.  The error is
independent of the remaining row frequency, exactly as in Lemma 5.3. -/
noncomputable def projectionErrorHMinusSq (q : Estimates.Parameters)
    (ell : ℝ → ℝ → ℂ) : ℝ :=
  Estimates.torusIntegral fun beta =>
    Estimates.torusIntegral fun r =>
      Estimates.mixedHMinusWeight q r beta * ‖projectionMixedError ell beta‖ ^ 2

/-- The multiplier energy of the discarded diagonal coefficient. -/
noncomputable def diagonalMultiplierEnergy (kappa : ℝ)
    (q : Estimates.Parameters) (ell : ℝ → ℝ → ℂ) : ℝ :=
  Estimates.torusIntegral fun beta =>
    Estimates.torusIntegral fun alpha =>
      Estimates.multiplier kappa q
        (Estimates.mixedTotalFrequency beta alpha) * ‖ell alpha beta‖ ^ 2

/-- The degree-two error carrier has no two-row component. -/
structure ProjectionErrorComponents where
  /-- The two-row component, which vanishes for the error carrier. -/
  twoRow : Type11Index → ℂ
  /-- The mixed component, as a function of the two frequencies. -/
  mixed : ℝ → ℝ → ℂ

/-- The frequency-space projection error associated with a discarded
diagonal coefficient. -/
noncomputable def projectionErrorComponents (ell : ℝ → ℝ → ℂ) :
    ProjectionErrorComponents where
  twoRow := 0
  mixed := fun _ beta => projectionMixedError ell beta

/-- Lemma 5.3's qualitative clause: the difference has only a mixed
component. -/
theorem projectionError_onlyMixed (ell : ℝ → ℝ → ℂ) :
    (projectionErrorComponents ell).twoRow = 0 := rfl

@[simp] theorem projectionError_mixed_apply (ell : ℝ → ℝ → ℂ)
    (r beta : ℝ) :
    (projectionErrorComponents ell).mixed r beta =
      projectionMixedError ell beta := rfl

/-- Identification surface for the concrete raw/projected lowering
difference. -/
def RawProjectionDifferenceIdentification
    (actualError : ProjectionErrorComponents) (ell : ℝ → ℝ → ℂ) : Prop :=
  actualError = projectionErrorComponents ell

/-- Any concretely identified raw/projected lowering difference has no
two-row component. -/
theorem rawProjectionDifference_onlyMixed
    (actualError : ProjectionErrorComponents) (ell : ℝ → ℝ → ℂ)
    (hidentify : RawProjectionDifferenceIdentification actualError ell) :
    actualError.twoRow = 0 := by
  rw [hidentify]
  exact projectionError_onlyMixed ell

private theorem sin_sq_le_two_mul_dispersion (x : ℝ) :
    Real.sin x ^ 2 ≤ 2 * Estimates.dispersion x := by
  unfold Estimates.dispersion
  rw [Real.sin_sq]
  nlinarith [Real.neg_one_le_cos x, Real.cos_le_one x]

/-- The line-resolvent factors in Lemma 5.3 collapse to at most one. -/
theorem projectionError_resolvent_factor_le_one {q : Estimates.Parameters}
    (hlambda : 0 < q.lambda) (beta : ℝ) :
    Real.sin beta ^ 2 *
        (Estimates.torusIntegral fun r : ℝ =>
          (q.lambda + Estimates.dispersion beta +
            Estimates.dispersion r)⁻¹) ^ 2 ≤ 1 := by
  let mu := q.lambda + Estimates.dispersion beta
  have hmu : 0 < mu :=
    add_pos_of_pos_of_nonneg hlambda (Estimates.dispersion_nonneg beta)
  have hline := Estimates.lineResolventIdentity_proved mu hmu
  have hsin : Real.sin beta ^ 2 ≤ 2 * mu := by
    dsimp [mu]
    linarith [sin_sq_le_two_mul_dispersion beta]
  have hmuTwo : 0 < mu + 2 := by linarith
  rw [show Estimates.torusIntegral (fun r : ℝ =>
      (q.lambda + Estimates.dispersion beta + Estimates.dispersion r)⁻¹) =
      (Real.sqrt (mu * (mu + 2)))⁻¹ by simpa [mu] using hline]
  rw [inv_pow]
  have hsqrtSq : Real.sqrt (mu * (mu + 2)) ^ 2 = mu * (mu + 2) :=
    Real.sq_sqrt (mul_nonneg hmu.le hmuTwo.le)
  rw [hsqrtSq]
  rw [← div_eq_mul_inv, div_le_one (mul_pos hmu hmuTwo)]
  nlinarith

/-- Pointwise domination of the basic diagonal energy by the paper's
multiplier. -/
theorem diagonalBasicWeight_le_multiplier {kappa : ℝ}
    {q : Estimates.Parameters} (hlambda : 0 ≤ q.lambda)
    (hkappa : 1 ≤ kappa)
    (alpha beta : ℝ) :
    q.lambda + Estimates.dispersion beta + Estimates.dispersion alpha ≤
      Estimates.multiplier kappa q
        (Estimates.mixedTotalFrequency beta alpha) := by
  unfold Estimates.multiplier Estimates.theta Estimates.mixedTotalFrequency
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  let w := q.lambda + Estimates.dispersion beta + Estimates.dispersion alpha
  let v := w + 2 * |Real.sin (beta / 2)| + 2 * |Real.sin (alpha / 2)|
  have hw : 0 ≤ w := by
    dsimp [w]
    linarith [Estimates.dispersion_nonneg beta,
      Estimates.dispersion_nonneg alpha]
  have hv : 0 ≤ v := by
    dsimp [v]
    linarith [hw, abs_nonneg (Real.sin (beta / 2)),
      abs_nonneg (Real.sin (alpha / 2))]
  have hbase :
      q.lambda + Estimates.dispersion beta + Estimates.dispersion alpha ≤
        q.lambda + Estimates.dispersion beta + Estimates.dispersion alpha +
          2 * |Real.sin (beta / 2)| + 2 * |Real.sin (alpha / 2)| := by
    linarith [abs_nonneg (Real.sin (beta / 2)),
      abs_nonneg (Real.sin (alpha / 2))]
  have hinner :
      q.lambda + (Estimates.dispersion beta + Estimates.dispersion alpha) +
          2 * |Real.sin (beta / 2)| + 2 * |Real.sin (alpha / 2)| = v := by
    dsimp [v, w]
    ring
  rw [hinner]
  exact hbase.trans (by
    change v ≤ kappa * v
    nlinarith [mul_nonneg (sub_nonneg.mpr hkappa) hv])

private theorem volume_torus_ne_top :
    volume Estimates.torus ≠ ⊤ := by
  simp [Estimates.torus]

/-- Weighted Cauchy--Schwarz on the normalized real torus.  The explicit
integrability hypotheses prevent any use of Lean's undefined-integral
branch. -/
theorem torusIntegral_norm_sq_le_weighted (mu : ℝ) (hmu : 0 < mu)
    (ell : ℝ → ℂ) (hell : Measurable ell)
    (hinv : Integrable (fun alpha : ℝ =>
      (mu + Estimates.dispersion alpha)⁻¹)
      (volume.restrict Estimates.torus))
    (henergy : Integrable (fun alpha : ℝ =>
      (mu + Estimates.dispersion alpha) * ‖ell alpha‖ ^ 2)
      (volume.restrict Estimates.torus)) :
    ‖Estimates.torusIntegral ell‖ ^ 2 ≤
      Estimates.torusIntegral (fun alpha : ℝ =>
        (mu + Estimates.dispersion alpha)⁻¹) *
      Estimates.torusIntegral (fun alpha : ℝ =>
        (mu + Estimates.dispersion alpha) * ‖ell alpha‖ ^ 2) := by
  let w : ℝ → ℝ := fun alpha => mu + Estimates.dispersion alpha
  let f : ℝ → ℝ := fun alpha => (Real.sqrt (w alpha))⁻¹
  let g : ℝ → ℝ := fun alpha => Real.sqrt (w alpha) * ‖ell alpha‖
  have hw : ∀ alpha, 0 < w alpha := fun alpha =>
    add_pos_of_pos_of_nonneg hmu (Estimates.dispersion_nonneg alpha)
  have hfmeas : Measurable f := by
    dsimp [f, w, Estimates.dispersion]
    fun_prop
  have hgmeas : Measurable g := by
    dsimp [g, w, Estimates.dispersion]
    fun_prop
  have hfsq : ∀ alpha, ‖f alpha‖ ^ 2 = (w alpha)⁻¹ := by
    intro alpha
    have hsqrt : 0 < Real.sqrt (w alpha) := Real.sqrt_pos.2 (hw alpha)
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hsqrt), inv_pow,
      Real.sq_sqrt (hw alpha).le]
  have hgsq : ∀ alpha, ‖g alpha‖ ^ 2 = w alpha * ‖ell alpha‖ ^ 2 := by
    intro alpha
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)), mul_pow,
      Real.sq_sqrt (hw alpha).le]
  have hfsqPlain : ∀ alpha, f alpha ^ 2 = (w alpha)⁻¹ := by
    intro alpha
    rw [← hfsq]
    congr 1
    exact (Real.norm_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))).symm
  have hgsqPlain : ∀ alpha, g alpha ^ 2 = w alpha * ‖ell alpha‖ ^ 2 := by
    intro alpha
    rw [← hgsq]
    congr 1
    exact (Real.norm_of_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).symm
  have hfmem : MemLp f 2 (volume.restrict Estimates.torus) := by
    apply (memLp_two_iff_integrable_sq_norm
      hfmeas.aestronglyMeasurable).2
    apply hinv.congr
    filter_upwards with alpha
    rw [hfsq]
  have hgmem : MemLp g 2 (volume.restrict Estimates.torus) := by
    apply (memLp_two_iff_integrable_sq_norm
      hgmeas.aestronglyMeasurable).2
    apply henergy.congr
    filter_upwards with alpha
    rw [hgsq]
  have hfactor : ∀ alpha, f alpha * g alpha = ‖ell alpha‖ := by
    intro alpha
    have hsqrt : 0 < Real.sqrt (w alpha) := Real.sqrt_pos.2 (hw alpha)
    dsimp [f, g]
    rw [← mul_assoc, inv_mul_cancel₀ hsqrt.ne', one_mul]
  have hfnonneg : 0 ≤ᵐ[volume.restrict Estimates.torus] f :=
    Filter.Eventually.of_forall fun alpha =>
      inv_nonneg.mpr (Real.sqrt_nonneg (w alpha))
  have hgnonneg : 0 ≤ᵐ[volume.restrict Estimates.torus] g :=
    Filter.Eventually.of_forall fun alpha =>
      mul_nonneg (Real.sqrt_nonneg (w alpha)) (norm_nonneg (ell alpha))
  have hfmem' : MemLp f (ENNReal.ofReal (2 : ℝ))
      (volume.restrict Estimates.torus) := by
    simpa using hfmem
  have hgmem' : MemLp g (ENNReal.ofReal (2 : ℝ))
      (volume.restrict Estimates.torus) := by
    simpa using hgmem
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    Real.HolderConjugate.two_two hfnonneg hgnonneg hfmem' hgmem'
  have hfint : (∫ alpha in Estimates.torus, f alpha ^ 2) =
      ∫ alpha in Estimates.torus, (w alpha)⁻¹ :=
    integral_congr_ae (Filter.Eventually.of_forall hfsqPlain)
  have hgint : (∫ alpha in Estimates.torus, g alpha ^ 2) =
      ∫ alpha in Estimates.torus, w alpha * ‖ell alpha‖ ^ 2 :=
    integral_congr_ae (Filter.Eventually.of_forall hgsqPlain)
  have hnormInt :
      ‖∫ alpha in Estimates.torus, ell alpha‖ ≤
        ∫ alpha in Estimates.torus, ‖ell alpha‖ :=
    norm_integral_le_integral_norm ell
  have hfg :
      (∫ alpha in Estimates.torus, ‖ell alpha‖) ≤
        Real.sqrt (∫ alpha in Estimates.torus, (w alpha)⁻¹) *
          Real.sqrt (∫ alpha in Estimates.torus,
            w alpha * ‖ell alpha‖ ^ 2) := by
    rw [← integral_congr_ae (Filter.Eventually.of_forall hfactor)]
    simp_rw [Real.rpow_two] at hholder
    rw [hfint, hgint] at hholder
    norm_num [← Real.sqrt_eq_rpow] at hholder
    exact hholder
  have hinvNonneg : 0 ≤ ∫ alpha in Estimates.torus, (w alpha)⁻¹ := by
    apply integral_nonneg
    intro alpha
    exact inv_nonneg.mpr (hw alpha).le
  have henergyNonneg :
      0 ≤ ∫ alpha in Estimates.torus, w alpha * ‖ell alpha‖ ^ 2 := by
    apply integral_nonneg
    intro alpha
    exact mul_nonneg (hw alpha).le (sq_nonneg _)
  have hsqrtInv : Real.sqrt (∫ alpha in Estimates.torus, (w alpha)⁻¹) ^ 2 =
      ∫ alpha in Estimates.torus, (w alpha)⁻¹ := Real.sq_sqrt hinvNonneg
  have hsqrtEnergy :
      Real.sqrt (∫ alpha in Estimates.torus, w alpha * ‖ell alpha‖ ^ 2) ^ 2 =
        ∫ alpha in Estimates.torus, w alpha * ‖ell alpha‖ ^ 2 :=
    Real.sq_sqrt henergyNonneg
  have hraw :
      ‖∫ alpha in Estimates.torus, ell alpha‖ ^ 2 ≤
        (∫ alpha in Estimates.torus, (w alpha)⁻¹) *
          (∫ alpha in Estimates.torus, w alpha * ‖ell alpha‖ ^ 2) := by
    have hle := hnormInt.trans hfg
    have hsquare := (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).2 hle
    rw [mul_pow, hsqrtInv, hsqrtEnergy] at hsquare
    exact hsquare
  unfold Estimates.torusIntegral
  simp only [smul_eq_mul]
  have hc : 0 ≤ (2 * Real.pi)⁻¹ := by positivity
  dsimp [w] at hraw ⊢
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc,
    mul_pow]
  calc
    (2 * Real.pi)⁻¹ ^ 2 *
          ‖∫ (r : ℝ) in Estimates.torus, ell r‖ ^ 2 ≤
        (2 * Real.pi)⁻¹ ^ 2 *
          ((∫ (r : ℝ) in Estimates.torus,
              (mu + Estimates.dispersion r)⁻¹) *
            ∫ (r : ℝ) in Estimates.torus,
              (mu + Estimates.dispersion r) * ‖ell r‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hraw (sq_nonneg _)
    _ = ((2 * Real.pi)⁻¹ *
          ∫ (r : ℝ) in Estimates.torus,
            (mu + Estimates.dispersion r)⁻¹) *
        ((2 * Real.pi)⁻¹ *
          ∫ (r : ℝ) in Estimates.torus,
            (mu + Estimates.dispersion r) * ‖ell r‖ ^ 2) := by ring

/-- The quantitative heart of Lemma 5.3, at one fixed column frequency.
The line-resolvent identity and weighted Cauchy--Schwarz give constant one
for every `kappa ≥ 1`. -/
theorem projectionError_slice_le_multiplier {kappa : ℝ}
    {q : Estimates.Parameters} (hlambda : 0 < q.lambda)
    (hkappa : 1 ≤ kappa) (ell : ℝ → ℝ → ℂ) (beta : ℝ)
    (hell : Measurable (fun alpha => ell alpha beta))
    (hmult : Integrable (fun alpha : ℝ =>
      Estimates.multiplier kappa q
          (Estimates.mixedTotalFrequency beta alpha) * ‖ell alpha beta‖ ^ 2)
      (volume.restrict Estimates.torus)) :
    Estimates.torusIntegral (fun r : ℝ =>
        Estimates.mixedHMinusWeight q r beta *
          ‖projectionMixedError ell beta‖ ^ 2) ≤
      Estimates.torusIntegral (fun alpha : ℝ =>
        Estimates.multiplier kappa q
          (Estimates.mixedTotalFrequency beta alpha) * ‖ell alpha beta‖ ^ 2) := by
  let mu := q.lambda + Estimates.dispersion beta
  let basic : ℝ → ℝ := fun alpha =>
    (mu + Estimates.dispersion alpha) * ‖ell alpha beta‖ ^ 2
  let mult : ℝ → ℝ := fun alpha =>
    Estimates.multiplier kappa q
      (Estimates.mixedTotalFrequency beta alpha) * ‖ell alpha beta‖ ^ 2
  have hmu : 0 < mu :=
    add_pos_of_pos_of_nonneg hlambda (Estimates.dispersion_nonneg beta)
  have hinvMeas : Measurable (fun alpha : ℝ =>
      (mu + Estimates.dispersion alpha)⁻¹) := by
    dsimp [mu, Estimates.dispersion]
    fun_prop
  have hinv : Integrable (fun alpha : ℝ =>
      (mu + Estimates.dispersion alpha)⁻¹)
      (volume.restrict Estimates.torus) := by
    apply Integrable.mono'
      (integrableOn_const (C := mu⁻¹) volume_torus_ne_top)
      hinvMeas.aestronglyMeasurable
    filter_upwards with alpha
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr
      (add_pos_of_pos_of_nonneg hmu (Estimates.dispersion_nonneg alpha)))]
    exact (inv_le_inv₀
      (add_pos_of_pos_of_nonneg hmu (Estimates.dispersion_nonneg alpha))
      hmu).2 (le_add_of_nonneg_right (Estimates.dispersion_nonneg alpha))
  have hbasicMeas : Measurable basic := by
    dsimp [basic, mu, Estimates.dispersion]
    fun_prop
  have hbasicNonneg : ∀ alpha, 0 ≤ basic alpha := by
    intro alpha
    exact mul_nonneg
      (add_pos_of_pos_of_nonneg hmu (Estimates.dispersion_nonneg alpha)).le
      (sq_nonneg _)
  have hmultNonneg : ∀ alpha, 0 ≤ mult alpha := by
    intro alpha
    apply mul_nonneg
    · exact Estimates.multiplier_nonneg (zero_le_one.trans hkappa) hlambda.le _
    · exact sq_nonneg _
  have hbasicLe : ∀ alpha, basic alpha ≤ mult alpha := by
    intro alpha
    apply mul_le_mul_of_nonneg_right
      (diagonalBasicWeight_le_multiplier hlambda.le hkappa alpha beta)
      (sq_nonneg _)
  have hbasic : Integrable basic (volume.restrict Estimates.torus) := by
    apply Integrable.mono' hmult hbasicMeas.aestronglyMeasurable
    filter_upwards with alpha
    rw [Real.norm_eq_abs, abs_of_nonneg (hbasicNonneg alpha)]
    simpa only [mult] using hbasicLe alpha
  have hcauchy := torusIntegral_norm_sq_le_weighted mu hmu
    (fun alpha => ell alpha beta) hell hinv (by simpa [basic] using hbasic)
  let R := Estimates.torusIntegral fun r : ℝ =>
    (mu + Estimates.dispersion r)⁻¹
  let E := Estimates.torusIntegral basic
  have hRNonneg : 0 ≤ R := by
    unfold R Estimates.torusIntegral
    simp only [smul_eq_mul]
    apply mul_nonneg (by positivity)
    apply integral_nonneg
    intro r
    exact inv_nonneg.mpr
      (add_pos_of_pos_of_nonneg hmu (Estimates.dispersion_nonneg r)).le
  have hENonneg : 0 ≤ E := by
    unfold E Estimates.torusIntegral
    simp only [smul_eq_mul]
    apply mul_nonneg (by positivity)
    exact integral_nonneg fun alpha => hbasicNonneg alpha
  have herrorNorm : ‖projectionMixedError ell beta‖ ^ 2 =
      Real.sin beta ^ 2 *
        ‖Estimates.torusIntegral (fun alpha => ell alpha beta)‖ ^ 2 := by
    unfold projectionMixedError
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  have hden : ∀ r, Estimates.mixedHMinusWeight q r beta =
      (mu + Estimates.dispersion r)⁻¹ := by
    intro r
    unfold Estimates.mixedHMinusWeight
    congr 1
    dsimp [mu]
    ring
  have hleft : Estimates.torusIntegral (fun r : ℝ =>
      Estimates.mixedHMinusWeight q r beta *
        ‖projectionMixedError ell beta‖ ^ 2) =
      R * ‖projectionMixedError ell beta‖ ^ 2 := by
    simp_rw [hden]
    unfold R Estimates.torusIntegral
    simp only [smul_eq_mul]
    rw [integral_mul_const]
    ring_nf
  have hfactor := projectionError_resolvent_factor_le_one hlambda beta
  have htoBasic :
      R * ‖projectionMixedError ell beta‖ ^ 2 ≤ E := by
    rw [herrorNorm]
    have hcauchy' :
        ‖Estimates.torusIntegral (fun alpha => ell alpha beta)‖ ^ 2 ≤ R * E := by
      simpa only [R, E, basic] using hcauchy
    have hsinNonneg : 0 ≤ Real.sin beta ^ 2 := sq_nonneg _
    calc
      R * (Real.sin beta ^ 2 *
          ‖Estimates.torusIntegral (fun alpha => ell alpha beta)‖ ^ 2) ≤
          R * (Real.sin beta ^ 2 * (R * E)) := by gcongr
      _ = (Real.sin beta ^ 2 * R ^ 2) * E := by ring
      _ ≤ 1 * E := by gcongr
      _ = E := one_mul E
  rw [hleft]
  apply htoBasic.trans
  unfold E Estimates.torusIntegral
  simp only [smul_eq_mul]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply integral_mono hbasic hmult
  exact hbasicLe

/-- Finiteness data needed to pass the pointwise projection-error estimate
through the outer normalized torus integral.  For the paper's explicit
correction these facts follow from its bounded measurable formula. -/
def ProjectionErrorIntegrable (kappa : ℝ) (q : Estimates.Parameters)
    (ell : ℝ → ℝ → ℂ) : Prop :=
  (∀ beta, Measurable (fun alpha => ell alpha beta)) ∧
  (∀ beta, Integrable (fun alpha : ℝ =>
      Estimates.multiplier kappa q
          (Estimates.mixedTotalFrequency beta alpha) * ‖ell alpha beta‖ ^ 2)
      (volume.restrict Estimates.torus)) ∧
  Integrable (fun beta : ℝ =>
      Estimates.torusIntegral fun r : ℝ =>
        Estimates.mixedHMinusWeight q r beta *
          ‖projectionMixedError ell beta‖ ^ 2)
    (volume.restrict Estimates.torus) ∧
  Integrable (fun beta : ℝ =>
      Estimates.torusIntegral fun alpha : ℝ =>
        Estimates.multiplier kappa q
          (Estimates.mixedTotalFrequency beta alpha) * ‖ell alpha beta‖ ^ 2)
    (volume.restrict Estimates.torus)

private theorem torusIntegral_mono {f g : ℝ → ℝ}
    (hf : Integrable f (volume.restrict Estimates.torus))
    (hg : Integrable g (volume.restrict Estimates.torus))
    (hfg : ∀ x, f x ≤ g x) :
    Estimates.torusIntegral f ≤ Estimates.torusIntegral g := by
  unfold Estimates.torusIntegral
  simp only [smul_eq_mul]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact integral_mono hf hg hfg

/-- Lemma 5.3 after integration in the remaining column frequency.  In the
Finset normalization the universal constant is one. -/
theorem projectionErrorHMinusSq_le_diagonalMultiplierEnergy {kappa : ℝ}
    {q : Estimates.Parameters} (hlambda : 0 < q.lambda)
    (hkappa : 1 ≤ kappa) (ell : ℝ → ℝ → ℂ)
    (hfinite : ProjectionErrorIntegrable kappa q ell) :
    projectionErrorHMinusSq q ell ≤
      diagonalMultiplierEnergy kappa q ell := by
  rcases hfinite with ⟨hell, hmult, herrorOuter, hmultOuter⟩
  unfold projectionErrorHMinusSq diagonalMultiplierEnergy
  exact torusIntegral_mono herrorOuter hmultOuter fun beta =>
    projectionError_slice_le_multiplier hlambda hkappa ell beta
      (hell beta) (hmult beta)

/-- The fixed multiplier `M` used by the correction satisfies the integrated
projection-error estimate with constant one. -/
theorem projectionErrorHMinusSq_le_diagonalMultiplierEnergy40
    {q : Estimates.Parameters} (hlambda : 0 < q.lambda)
    (ell : ℝ → ℝ → ℂ)
    (hfinite : ProjectionErrorIntegrable 40 q ell) :
    projectionErrorHMinusSq q ell ≤
      diagonalMultiplierEnergy 40 q ell :=
  projectionErrorHMinusSq_le_diagonalMultiplierEnergy hlambda (by norm_num)
    ell hfinite

/-- Weighted contractivity bridge from the diagonal error energy to the full
raw multiplier energy. -/
def RawProjectionEnergyBound (q : Estimates.Parameters)
    (ell : ℝ → ℝ → ℂ) (rawEnergy : ℝ) : Prop :=
  diagonalMultiplierEnergy 40 q ell ≤ rawEnergy

/-- Full Lemma 5.3 estimate once the raw Fourier coefficient is identified
with its diagonal projection complement. -/
theorem projectionErrorHMinusSq_le_rawMultiplierEnergy
    {q : Estimates.Parameters} (hlambda : 0 < q.lambda)
    (ell : ℝ → ℝ → ℂ) (rawEnergy : ℝ)
    (hfinite : ProjectionErrorIntegrable 40 q ell)
    (hraw : RawProjectionEnergyBound q ell rawEnergy) :
    projectionErrorHMinusSq q ell ≤ rawEnergy :=
  (projectionErrorHMinusSq_le_diagonalMultiplierEnergy40 hlambda ell
    hfinite).trans hraw

end

end Manhattan.Glue
