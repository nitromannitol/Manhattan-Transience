import Manhattan.Glue.CubicDischargeTorus

/-!
# Discharge of the cubic multiplier interface

The raw type-`112` coefficient of the paper is the symmetrization of a single
summand, and Step 1 of Lemma 5.4 shows that the two summands have disjoint
supports. Consequently the raw multiplier energy is exactly twice the scalar
quantity `correctionSigmaEnergy`.

Paper: `manuscript.tex:1045-1052` (the coefficient), `manuscript.tex:1314-1330`
(Step 1 and equation (30)).
-/

open MeasureTheory Set

namespace Manhattan.Glue

noncomputable section

local instance cubicDischargePropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-! ### The two disjoint summands -/

/-- The reciprocal multiplier restricted to the interval `J(r,β)`. -/
def correctionIntervalWeight (kappa : ℝ) (q : Estimates.Parameters)
    (a r beta alpha : ℝ) : ℝ :=
  if alpha ∈ Estimates.correctionInterval q a r beta then
    (Estimates.multiplier kappa q
      (Estimates.mixedTotalFrequency beta alpha))⁻¹
  else 0

theorem correctionSigma_eq_weight (kappa : ℝ) (q : Estimates.Parameters)
    (a r beta : ℝ) :
    Estimates.correctionSigma kappa q a r beta =
      Real.sin beta ^ 2 *
        Estimates.torusIntegral
          (fun alpha => correctionIntervalWeight kappa q a r beta alpha) := rfl

/-- One symmetrized summand of the multiplier energy density of the raw
type-`112` coefficient. -/
def cubicSplitDensity (kappa : ℝ) (q : Estimates.Parameters)
    (a p₂ r r' beta : ℝ) : ℝ :=
  Real.sin beta ^ 2 * Estimates.correctionV kappa q a r beta ^ 2 *
    correctionIntervalWeight kappa q a r beta (r + r' - p₂)

theorem cubicSplitDensity_swap (kappa : ℝ) (q : Estimates.Parameters)
    (a p₂ r r' beta : ℝ) :
    cubicSplitDensity kappa q a p₂ r' r beta =
      Real.sin beta ^ 2 * Estimates.correctionV kappa q a r' beta ^ 2 *
        correctionIntervalWeight kappa q a r' beta (r + r' - p₂) := by
  unfold cubicSplitDensity
  rw [show r' + r - p₂ = r + r' - p₂ by ring]

/-- Step 1 of Lemma 5.4: the two symmetrized summands of the raw type-`112`
coefficient have disjoint supports. -/
theorem correctionInterval_disjoint {q : Estimates.Parameters}
    (hlambda : 0 < q.lambda) (hK : 1 ≤ q.K) {a p₂ : ℝ} (ha : 0 ≤ a)
    (hp₂ : |p₂| ≤ a) (r r' beta : ℝ)
    (h1 : r + r' - p₂ ∈ Estimates.correctionInterval q a r beta)
    (h2 : r + r' - p₂ ∈ Estimates.correctionInterval q a r' beta) : False := by
  classical
  have hdelta : 0 < q.delta a := by
    have hsq : 0 < Real.sqrt q.lambda := Real.sqrt_pos.2 hlambda
    unfold Estimates.Parameters.delta
    linarith
  rw [Estimates.correctionInterval] at h1 h2
  split_ifs at h1 with hc1
  · split_ifs at h2 with hc2
    · rw [mem_Icc] at h1 h2
      have hr : q.K * q.delta a ≤ r := (mem_Icc.mp hc1.1).1
      have hr' : q.K * q.delta a ≤ r' := (mem_Icc.mp hc2.1).1
      have hKd : q.delta a ≤ q.K * q.delta a := by nlinarith
      have hp : p₂ ≤ a := le_trans (le_abs_self p₂) hp₂
      have hadelta : a ≤ q.delta a := by
        unfold Estimates.Parameters.delta
        linarith [Real.sqrt_nonneg q.lambda]
      have hpos : 0 < r + r' - p₂ := by linarith
      have hbetaNonneg : (0:ℝ) ≤ |beta| := abs_nonneg beta
      have hneg : r + r' - p₂ ≤ -4 * q.K * (r + q.delta a + |beta|) := h1.2
      nlinarith
    · exact absurd h2 (by simp)
  · exact absurd h1 (by simp)

/-- Equation (30): the multiplier energy density of the raw coefficient is
the sum of the two disjoint summands. -/
theorem multiplier_mul_norm_correctionCoefficient_sq {kappa : ℝ}
    {q : Estimates.Parameters} (hkappa : 0 < kappa) (hlambda : 0 < q.lambda)
    (hK : 1 ≤ q.K) {a p₂ : ℝ} (ha : 0 ≤ a) (hp₂ : |p₂| ≤ a) (r r' beta : ℝ) :
    Estimates.multiplier kappa q
        (Estimates.mixedTotalFrequency beta (r + r' - p₂)) *
        ‖Estimates.correctionCoefficient kappa q a p₂ r r' beta‖ ^ 2 =
      cubicSplitDensity kappa q a p₂ r r' beta +
        cubicSplitDensity kappa q a p₂ r' r beta := by
  classical
  have hMpos : 0 < Estimates.multiplier kappa q
      (Estimates.mixedTotalFrequency beta (r + r' - p₂)) :=
    Estimates.multiplier_pos hkappa hlambda _
  rw [cubicSplitDensity_swap kappa q a p₂ r r' beta]
  unfold cubicSplitDensity correctionIntervalWeight
  simp only [Estimates.correctionCoefficient]
  by_cases h1 : r + r' - p₂ ∈ Estimates.correctionInterval q a r beta <;>
    by_cases h2 : r + r' - p₂ ∈ Estimates.correctionInterval q a r' beta
  · exact absurd h2 (fun h =>
      correctionInterval_disjoint hlambda hK ha hp₂ r r' beta h1 h)
  · rw [if_pos h1, if_neg h2, if_pos h1, if_neg h2]
    have hrw : (Complex.I * (Real.sin beta : ℂ) /
        ((Estimates.multiplier kappa q
          (Estimates.mixedTotalFrequency beta (r + r' - p₂)) : ℝ) : ℂ) *
        ((Estimates.correctionV kappa q a r beta : ℂ) * 1 +
          (Estimates.correctionV kappa q a r' beta : ℂ) * 0)) =
        Complex.I * (Real.sin beta : ℂ) *
          (Estimates.correctionV kappa q a r beta : ℂ) /
          ((Estimates.multiplier kappa q
            (Estimates.mixedTotalFrequency beta (r + r' - p₂)) : ℝ) : ℂ) := by
      ring
    rw [hrw, norm_div, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
      Complex.norm_real, Complex.norm_real]
    simp only [Real.norm_eq_abs, one_mul, div_pow, mul_pow, sq_abs,
      abs_of_pos hMpos]
    field_simp
    ring
  · rw [if_neg h1, if_pos h2, if_neg h1, if_pos h2]
    have hrw : (Complex.I * (Real.sin beta : ℂ) /
        ((Estimates.multiplier kappa q
          (Estimates.mixedTotalFrequency beta (r + r' - p₂)) : ℝ) : ℂ) *
        ((Estimates.correctionV kappa q a r beta : ℂ) * 0 +
          (Estimates.correctionV kappa q a r' beta : ℂ) * 1)) =
        Complex.I * (Real.sin beta : ℂ) *
          (Estimates.correctionV kappa q a r' beta : ℂ) /
          ((Estimates.multiplier kappa q
            (Estimates.mixedTotalFrequency beta (r + r' - p₂)) : ℝ) : ℂ) := by
      ring
    rw [hrw, norm_div, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
      Complex.norm_real, Complex.norm_real]
    simp only [Real.norm_eq_abs, one_mul, div_pow, mul_pow, sq_abs,
      abs_of_pos hMpos]
    field_simp
    ring
  · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2]
    simp


/-! ### Bounds and measurability -/

theorem multiplier_lower {kappa : ℝ} {q : Estimates.Parameters}
    (hkappa : 0 ≤ kappa) (P : Fin 2 → ℝ) :
    kappa * q.lambda ≤ Estimates.multiplier kappa q P := by
  unfold Estimates.multiplier
  apply mul_le_mul_of_nonneg_left _ hkappa
  have h := Estimates.theta_nonneg P
  have h0 : (0:ℝ) ≤ |Real.sin (P 0 / 2)| := abs_nonneg _
  have h1 : (0:ℝ) ≤ |Real.sin (P 1 / 2)| := abs_nonneg _
  linarith

theorem correctionIntervalWeight_nonneg {kappa : ℝ} {q : Estimates.Parameters}
    (hkappa : 0 < kappa) (hlambda : 0 < q.lambda) (a r beta alpha : ℝ) :
    0 ≤ correctionIntervalWeight kappa q a r beta alpha := by
  classical
  unfold correctionIntervalWeight
  split_ifs
  · exact (inv_pos.2 (Estimates.multiplier_pos hkappa hlambda _)).le
  · exact le_rfl

theorem correctionIntervalWeight_le {kappa : ℝ} {q : Estimates.Parameters}
    (hkappa : 0 < kappa) (hlambda : 0 < q.lambda) (a r beta alpha : ℝ) :
    correctionIntervalWeight kappa q a r beta alpha ≤ (kappa * q.lambda)⁻¹ := by
  classical
  unfold correctionIntervalWeight
  have hprod : 0 < kappa * q.lambda := mul_pos hkappa hlambda
  split_ifs
  · exact (inv_le_inv₀ (Estimates.multiplier_pos hkappa hlambda _) hprod).2
      (multiplier_lower hkappa.le _)
  · exact (inv_pos.2 hprod).le

/-- Outside a short interval around the origin the interval weight
vanishes. -/
theorem correctionIntervalWeight_support {kappa : ℝ}
    {q : Estimates.Parameters} (hK : 1 ≤ q.K) {a : ℝ} (ha : 0 ≤ a)
    (hlambda : 0 < q.lambda) (r beta : ℝ) (s : ℝ)
    (hs : s ∉ Icc (-q.rho) 0) :
    correctionIntervalWeight kappa q a r beta s = 0 := by
  classical
  unfold correctionIntervalWeight
  rw [if_neg]
  intro hmem
  apply hs
  rw [Estimates.correctionInterval] at hmem
  split_ifs at hmem with hc
  · rw [mem_Icc] at hmem ⊢
    refine ⟨hmem.1, ?_⟩
    have hdelta : 0 < q.delta a := by
      have hsq : 0 < Real.sqrt q.lambda := Real.sqrt_pos.2 hlambda
      unfold Estimates.Parameters.delta
      linarith
    have hr : q.K * q.delta a ≤ r := (mem_Icc.mp hc.1).1
    have hbeta : (0:ℝ) ≤ |beta| := abs_nonneg beta
    have hKd : q.delta a ≤ q.K * q.delta a := by nlinarith
    have hle : s ≤ -4 * q.K * (r + q.delta a + |beta|) := hmem.2
    nlinarith
  · exact absurd hmem (by simp)

theorem cubicSplitDensity_nonneg {kappa : ℝ} {q : Estimates.Parameters}
    (hkappa : 0 < kappa) (hlambda : 0 < q.lambda) (a p₂ r r' beta : ℝ) :
    0 ≤ cubicSplitDensity kappa q a p₂ r r' beta := by
  unfold cubicSplitDensity
  exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (correctionIntervalWeight_nonneg hkappa hlambda a r beta _)

theorem abs_cubicSplitDensity_le {kappa : ℝ} {q : Estimates.Parameters}
    (hkappa : 0 < kappa) (hlambda : 0 < q.lambda) (a p₂ r r' beta : ℝ) :
    |cubicSplitDensity kappa q a p₂ r r' beta| ≤
      q.lambda⁻¹ ^ 2 * (kappa * q.lambda)⁻¹ := by
  rw [abs_of_nonneg (cubicSplitDensity_nonneg hkappa hlambda a p₂ r r' beta)]
  unfold cubicSplitDensity
  have hsin : Real.sin beta ^ 2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq beta, sq_nonneg (Real.cos beta)]
  have hv : |Estimates.correctionV kappa q a r beta| ≤ q.lambda⁻¹ :=
    abs_correctionV_le_inv hkappa hlambda a r beta
  have hvsq : Estimates.correctionV kappa q a r beta ^ 2 ≤ q.lambda⁻¹ ^ 2 := by
    rw [← sq_abs]
    have h0 : (0:ℝ) ≤ q.lambda⁻¹ := inv_nonneg.2 hlambda.le
    nlinarith [abs_nonneg (Estimates.correctionV kappa q a r beta)]
  have hW := correctionIntervalWeight_le hkappa hlambda a r beta (r + r' - p₂)
  have hWnonneg :=
    correctionIntervalWeight_nonneg hkappa hlambda a r beta (r + r' - p₂)
  have hvsqNonneg : (0:ℝ) ≤ Estimates.correctionV kappa q a r beta ^ 2 :=
    sq_nonneg _
  calc Real.sin beta ^ 2 * Estimates.correctionV kappa q a r beta ^ 2 *
        correctionIntervalWeight kappa q a r beta (r + r' - p₂)
      ≤ 1 * q.lambda⁻¹ ^ 2 * (kappa * q.lambda)⁻¹ :=
        mul_le_mul (mul_le_mul hsin hvsq hvsqNonneg (by norm_num)) hW
          hWnonneg (by positivity)
    _ = q.lambda⁻¹ ^ 2 * (kappa * q.lambda)⁻¹ := by ring

theorem torusIntegral_measurable_single {f : ℝ → ℝ → ℝ}
    (hf : Measurable fun z : ℝ × ℝ => f z.1 z.2) :
    Measurable fun x : ℝ => Estimates.torusIntegral fun b => f x b := by
  have h := torusIntegral_measurable_prod
    (f := fun z : ℝ × ℝ => fun b : ℝ => f z.1 b)
    (by
      have hcomp : (fun w : (ℝ × ℝ) × ℝ => f w.1.1 w.2)
          = (fun z : ℝ × ℝ => f z.1 z.2) ∘
            (fun w : (ℝ × ℝ) × ℝ => (w.1.1, w.2)) := rfl
      rw [hcomp]
      exact hf.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  exact h.comp (measurable_id.prodMk (measurable_const (a := (0:ℝ))))

theorem cubicSplitDensity_measurable (kappa : ℝ) (q : Estimates.Parameters)
    (a p₂ : ℝ) :
    Measurable fun z : ℝ × ℝ × ℝ =>
      cubicSplitDensity kappa q a p₂ z.1 z.2.1 z.2.2 := by
  classical
  have hr : Measurable fun z : ℝ × ℝ × ℝ => z.1 := measurable_fst
  have hr' : Measurable fun z : ℝ × ℝ × ℝ => z.2.1 :=
    measurable_fst.comp measurable_snd
  have hbeta : Measurable fun z : ℝ × ℝ × ℝ => z.2.2 :=
    measurable_snd.comp measurable_snd
  have hset : MeasurableSet {z : ℝ × ℝ × ℝ |
      z.1 + z.2.1 - p₂ ∈ Estimates.correctionInterval q a z.1 z.2.2} := by
    unfold Estimates.correctionInterval Estimates.Parameters.supportInterval
      Estimates.Parameters.delta Estimates.Parameters.r0
    measurability
  have hv : Measurable fun z : ℝ × ℝ × ℝ =>
      Estimates.correctionV kappa q a z.1 z.2.2 :=
    (correctionV_measurable kappa q a).comp (hr.prodMk hbeta)
  have hmult : Measurable fun z : ℝ × ℝ × ℝ =>
      (Estimates.multiplier kappa q
        (Estimates.mixedTotalFrequency z.2.2 (z.1 + z.2.1 - p₂)))⁻¹ := by
    simp only [Estimates.multiplier, Estimates.mixedTotalFrequency,
      Estimates.theta, Estimates.dispersion, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    fun_prop
  unfold cubicSplitDensity correctionIntervalWeight
  exact (((Real.continuous_sin.measurable.comp hbeta).pow_const 2).mul
    (hv.pow_const 2)).mul (Measurable.ite hset hmult measurable_const)

/-! ### The inner column-frequency integral -/

/-- Integrating the summand in the second row frequency produces exactly the
logarithmic correction `σ` of (31) times `|v|²`. This is the change of
variables `α = r+r'-p₂` in Step 2 of Lemma 5.4. -/
theorem cubicSplitDensity_integral_r' {kappa : ℝ} {q : Estimates.Parameters}
    (hlambda : 0 < q.lambda) (hK : 1 ≤ q.K) (hrho : 0 ≤ q.rho)
    (hrhopi : 3 * q.rho < Real.pi) {a p₂ : ℝ} (ha : 0 ≤ a) (hp₂ : |p₂| ≤ a)
    (r beta : ℝ) :
    (Estimates.torusIntegral fun r' => cubicSplitDensity kappa q a p₂ r r' beta)
      = Estimates.correctionSigma kappa q a r beta *
          Estimates.correctionV kappa q a r beta ^ 2 := by
  classical
  have hrewrite : (fun r' : ℝ => cubicSplitDensity kappa q a p₂ r r' beta) =
      fun r' : ℝ => (Real.sin beta ^ 2 *
        Estimates.correctionV kappa q a r beta ^ 2) *
        correctionIntervalWeight kappa q a r beta ((r - p₂) + r') := by
    funext r'
    unfold cubicSplitDensity
    rw [show r + r' - p₂ = (r - p₂) + r' by ring]
  rw [hrewrite, cubicTorusIntegral_const_mul, correctionSigma_eq_weight]
  by_cases hr : r ∈ q.supportInterval a
  · have hcbound : |r - p₂| ≤ q.rho := by
      have hdelta : 0 < q.delta a := by
        have hsq : 0 < Real.sqrt q.lambda := Real.sqrt_pos.2 hlambda
        unfold Estimates.Parameters.delta
        linarith
      have hlow : q.K * q.delta a ≤ r := (mem_Icc.mp hr).1
      have hhigh : r ≤ q.r0 := (mem_Icc.mp hr).2
      have hr0 : q.r0 = q.rho / (100 * q.K) := rfl
      have hKpos : (0:ℝ) < q.K := by linarith
      have hrpos : 0 < r := by nlinarith
      have hadelta : a ≤ q.delta a := by
        unfold Estimates.Parameters.delta
        linarith [Real.sqrt_nonneg q.lambda]
      have hp : |p₂| ≤ q.delta a := le_trans hp₂ hadelta
      have hdr : q.delta a ≤ r := by nlinarith
      have hrsmall : r ≤ q.rho / (100 * q.K) := by rw [← hr0]; exact hhigh
      have h100 : q.rho / (100 * q.K) ≤ q.rho / 100 :=
        div_le_div_of_nonneg_left hrho (by norm_num) (by linarith)
      have hsmall : r ≤ q.rho / 100 := le_trans hrsmall h100
      have habs := abs_le.mp hp
      rw [abs_le]
      constructor <;> nlinarith
    rw [torusIntegral_translate (rho := q.rho) hrhopi hcbound
      (fun s hs => correctionIntervalWeight_support hK ha hlambda r beta s hs)]
    ring
  · have hv : Estimates.correctionV kappa q a r beta = 0 := by
      simp [Estimates.correctionV, hr]
    rw [hv]
    ring


/-! ### Measurability of the slices of the split density -/

section Slices

variable (kappa : ℝ) (q : Estimates.Parameters) (a p₂ : ℝ)

theorem cubicSplitDensity_measurable_swap :
    Measurable fun z : ℝ × ℝ × ℝ =>
      cubicSplitDensity kappa q a p₂ z.2.1 z.1 z.2.2 := by
  have hcomp : (fun z : ℝ × ℝ × ℝ => cubicSplitDensity kappa q a p₂ z.2.1 z.1 z.2.2)
      = (fun z : ℝ × ℝ × ℝ => cubicSplitDensity kappa q a p₂ z.1 z.2.1 z.2.2) ∘
        (fun z : ℝ × ℝ × ℝ => (z.2.1, z.1, z.2.2)) := rfl
  rw [hcomp]
  exact (cubicSplitDensity_measurable kappa q a p₂).comp
    ((measurable_fst.comp measurable_snd).prodMk
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))

theorem cubicSplitDensity_measurable_slice (r r' : ℝ) :
    Measurable fun b : ℝ => cubicSplitDensity kappa q a p₂ r r' b := by
  have hcomp : (fun b : ℝ => cubicSplitDensity kappa q a p₂ r r' b)
      = (fun z : ℝ × ℝ × ℝ => cubicSplitDensity kappa q a p₂ z.1 z.2.1 z.2.2) ∘
        (fun b : ℝ => (r, r', b)) := rfl
  rw [hcomp]
  exact (cubicSplitDensity_measurable kappa q a p₂).comp
    (measurable_const.prodMk (measurable_const.prodMk measurable_id))

theorem cubicSplitDensity_measurable_pairFirst (r : ℝ) :
    Measurable fun z : ℝ × ℝ => cubicSplitDensity kappa q a p₂ r z.1 z.2 := by
  have hcomp : (fun z : ℝ × ℝ => cubicSplitDensity kappa q a p₂ r z.1 z.2)
      = (fun z : ℝ × ℝ × ℝ => cubicSplitDensity kappa q a p₂ z.1 z.2.1 z.2.2) ∘
        (fun z : ℝ × ℝ => (r, z.1, z.2)) := rfl
  rw [hcomp]
  exact (cubicSplitDensity_measurable kappa q a p₂).comp
    (measurable_const.prodMk (measurable_fst.prodMk measurable_snd))

theorem cubicSplitDensity_measurable_pairSecond (r : ℝ) :
    Measurable fun z : ℝ × ℝ => cubicSplitDensity kappa q a p₂ z.1 r z.2 := by
  have hcomp : (fun z : ℝ × ℝ => cubicSplitDensity kappa q a p₂ z.1 r z.2)
      = (fun z : ℝ × ℝ × ℝ => cubicSplitDensity kappa q a p₂ z.1 z.2.1 z.2.2) ∘
        (fun z : ℝ × ℝ => (z.1, r, z.2)) := rfl
  rw [hcomp]
  exact (cubicSplitDensity_measurable kappa q a p₂).comp
    (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))

theorem cubicSplitDensity_measurable_prodPair :
    Measurable fun w : (ℝ × ℝ) × ℝ =>
      cubicSplitDensity kappa q a p₂ w.1.1 w.1.2 w.2 := by
  have hcomp : (fun w : (ℝ × ℝ) × ℝ =>
        cubicSplitDensity kappa q a p₂ w.1.1 w.1.2 w.2)
      = (fun z : ℝ × ℝ × ℝ => cubicSplitDensity kappa q a p₂ z.1 z.2.1 z.2.2) ∘
        (fun w : (ℝ × ℝ) × ℝ => (w.1.1, w.1.2, w.2)) := rfl
  rw [hcomp]
  exact (cubicSplitDensity_measurable kappa q a p₂).comp
    ((measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd))

theorem cubicSplitDensity_measurable_prodPairSwap :
    Measurable fun w : (ℝ × ℝ) × ℝ =>
      cubicSplitDensity kappa q a p₂ w.1.2 w.1.1 w.2 := by
  have hcomp : (fun w : (ℝ × ℝ) × ℝ =>
        cubicSplitDensity kappa q a p₂ w.1.2 w.1.1 w.2)
      = (fun z : ℝ × ℝ × ℝ => cubicSplitDensity kappa q a p₂ z.1 z.2.1 z.2.2) ∘
        (fun w : (ℝ × ℝ) × ℝ => (w.1.2, w.1.1, w.2)) := rfl
  rw [hcomp]
  exact (cubicSplitDensity_measurable kappa q a p₂).comp
    ((measurable_snd.comp measurable_fst).prodMk
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd))

theorem cubicSplitDensity_innerFirst_measurable (r : ℝ) :
    Measurable fun r' : ℝ =>
      Estimates.torusIntegral fun b => cubicSplitDensity kappa q a p₂ r r' b :=
  torusIntegral_measurable_single (cubicSplitDensity_measurable_pairFirst kappa q a p₂ r)

theorem cubicSplitDensity_innerSecond_measurable (r : ℝ) :
    Measurable fun r' : ℝ =>
      Estimates.torusIntegral fun b => cubicSplitDensity kappa q a p₂ r' r b :=
  torusIntegral_measurable_single (cubicSplitDensity_measurable_pairSecond kappa q a p₂ r)

theorem cubicSplitDensity_innerPair_measurable :
    Measurable fun z : ℝ × ℝ =>
      Estimates.torusIntegral fun b => cubicSplitDensity kappa q a p₂ z.1 z.2 b :=
  torusIntegral_measurable_prod (cubicSplitDensity_measurable_prodPair kappa q a p₂)

theorem cubicSplitDensity_innerPairSwap_measurable :
    Measurable fun z : ℝ × ℝ =>
      Estimates.torusIntegral fun b => cubicSplitDensity kappa q a p₂ z.2 z.1 b :=
  torusIntegral_measurable_prod (cubicSplitDensity_measurable_prodPairSwap kappa q a p₂)

theorem cubicSplitDensity_double_measurable :
    Measurable fun r : ℝ => Estimates.torusIntegral fun r' =>
      Estimates.torusIntegral fun b => cubicSplitDensity kappa q a p₂ r r' b :=
  torusIntegral_measurable_single (cubicSplitDensity_innerPair_measurable kappa q a p₂)

theorem cubicSplitDensity_doubleSwap_measurable :
    Measurable fun r : ℝ => Estimates.torusIntegral fun r' =>
      Estimates.torusIntegral fun b => cubicSplitDensity kappa q a p₂ r' r b :=
  torusIntegral_measurable_single (cubicSplitDensity_innerPairSwap_measurable kappa q a p₂)


end Slices


/-! ### Slices at a fixed column frequency -/

section RowSlices

variable (kappa : ℝ) (q : Estimates.Parameters) (a p₂ : ℝ)

theorem cubicSplitDensity_measurable_rowPair (beta : ℝ) :
    Measurable fun z : ℝ × ℝ => cubicSplitDensity kappa q a p₂ z.1 z.2 beta := by
  have hcomp : (fun z : ℝ × ℝ => cubicSplitDensity kappa q a p₂ z.1 z.2 beta)
      = (fun z : ℝ × ℝ × ℝ => cubicSplitDensity kappa q a p₂ z.1 z.2.1 z.2.2) ∘
        (fun z : ℝ × ℝ => (z.1, z.2, beta)) := rfl
  rw [hcomp]
  exact (cubicSplitDensity_measurable kappa q a p₂).comp
    (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))

theorem cubicSplitDensity_measurable_rowPairSwap (beta : ℝ) :
    Measurable fun z : ℝ × ℝ => cubicSplitDensity kappa q a p₂ z.2 z.1 beta := by
  have hcomp : (fun z : ℝ × ℝ => cubicSplitDensity kappa q a p₂ z.2 z.1 beta)
      = (fun z : ℝ × ℝ × ℝ => cubicSplitDensity kappa q a p₂ z.1 z.2.1 z.2.2) ∘
        (fun z : ℝ × ℝ => (z.2, z.1, beta)) := rfl
  rw [hcomp]
  exact (cubicSplitDensity_measurable kappa q a p₂).comp
    (measurable_snd.prodMk (measurable_fst.prodMk measurable_const))

theorem cubicSplitDensity_measurable_rowSecond (r beta : ℝ) :
    Measurable fun r' : ℝ => cubicSplitDensity kappa q a p₂ r r' beta := by
  have hcomp : (fun r' : ℝ => cubicSplitDensity kappa q a p₂ r r' beta)
      = (fun z : ℝ × ℝ => cubicSplitDensity kappa q a p₂ z.1 z.2 beta) ∘
        (fun r' : ℝ => (r, r')) := rfl
  rw [hcomp]
  exact (cubicSplitDensity_measurable_rowPair kappa q a p₂ beta).comp
    (measurable_const.prodMk measurable_id)

theorem cubicSplitDensity_measurable_rowFirst (r beta : ℝ) :
    Measurable fun r' : ℝ => cubicSplitDensity kappa q a p₂ r' r beta := by
  have hcomp : (fun r' : ℝ => cubicSplitDensity kappa q a p₂ r' r beta)
      = (fun z : ℝ × ℝ => cubicSplitDensity kappa q a p₂ z.2 z.1 beta) ∘
        (fun r' : ℝ => (r, r')) := rfl
  rw [hcomp]
  exact (cubicSplitDensity_measurable_rowPairSwap kappa q a p₂ beta).comp
    (measurable_const.prodMk measurable_id)

theorem cubicSplitDensity_innerRow_measurable (beta : ℝ) :
    Measurable fun r : ℝ =>
      Estimates.torusIntegral fun r' =>
        cubicSplitDensity kappa q a p₂ r r' beta :=
  torusIntegral_measurable_single
    (cubicSplitDensity_measurable_rowPair kappa q a p₂ beta)

theorem cubicSplitDensity_innerRowSwap_measurable (beta : ℝ) :
    Measurable fun r : ℝ =>
      Estimates.torusIntegral fun r' =>
        cubicSplitDensity kappa q a p₂ r' r beta :=
  torusIntegral_measurable_single
    (cubicSplitDensity_measurable_rowPairSwap kappa q a p₂ beta)

end RowSlices

/-! ### Equation (30): the raw multiplier energy is twice the scalar energy -/

section RawEnergy

attribute [local instance] Real.fact_zero_lt_one
attribute [local instance] cubicUnitAddCircleMeasureSpace

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem correctionSigmaEnergy_eq_double (q : Estimates.Parameters) (a : ℝ) :
    correctionSigmaEnergy q a =
      Estimates.torusIntegral fun r => Estimates.torusIntegral fun beta =>
        Estimates.correctionSigma 40 q a r beta *
          Estimates.correctionV 40 q a r beta ^ 2 := rfl

set_option maxHeartbeats 1000000 in
/-- Equation (30): the raw multiplier energy of the symmetrized type-`112`
coefficient is exactly twice the scalar energy of one summand. -/
theorem rawCubicMultiplierEnergy_eq_two_correctionSigmaEnergy
    {q : Estimates.Parameters} (hlambda : 0 < q.lambda) (hK : 1 ≤ q.K)
    (hrho : 0 ≤ q.rho) (hrhopi : 3 * q.rho < Real.pi)
    {a p₂ : ℝ} (ha : 0 ≤ a) (hp₂ : |p₂| ≤ a) :
    rawCubicMultiplierEnergy q a p₂ = 2 * correctionSigmaEnergy q a := by
  have hkappa : (0:ℝ) < 40 := by norm_num
  have hbound : ∀ r r' b : ℝ,
      |cubicSplitDensity 40 q a p₂ r r' b| ≤
        q.lambda⁻¹ ^ 2 * ((40:ℝ) * q.lambda)⁻¹ :=
    fun r r' b => abs_cubicSplitDensity_le hkappa hlambda a p₂ r r' b
  have hinnerBound : ∀ r r' : ℝ,
      |Estimates.torusIntegral fun b => cubicSplitDensity 40 q a p₂ r r' b| ≤
        q.lambda⁻¹ ^ 2 * ((40:ℝ) * q.lambda)⁻¹ :=
    fun r r' => abs_torusIntegral_le (fun b => hbound r r' b)
  have step0 : rawCubicMultiplierEnergy q a p₂
      = Estimates.torusIntegral fun r => Estimates.torusIntegral fun r' =>
          Estimates.torusIntegral fun b =>
            cubicSplitDensity 40 q a p₂ r r' b +
              cubicSplitDensity 40 q a p₂ r' r b := by
    unfold rawCubicMultiplierEnergy
    refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun x =>
      multiplier_mul_norm_correctionCoefficient_sq hkappa hlambda hK ha hp₂
        (unitTorusAngle (x 0)) (unitTorusAngle (x 1))
        (unitTorusAngle (x 2)))) ?_
    exact integral_unitTorus_three
      (fun r r' b => cubicSplitDensity 40 q a p₂ r r' b +
        cubicSplitDensity 40 q a p₂ r' r b)
      ((cubicSplitDensity_measurable 40 q a p₂).add
        (cubicSplitDensity_measurable_swap 40 q a p₂))
      (C := (q.lambda⁻¹ ^ 2 * ((40:ℝ) * q.lambda)⁻¹) +
        (q.lambda⁻¹ ^ 2 * ((40:ℝ) * q.lambda)⁻¹))
      (fun r r' b => (abs_add_le _ _).trans
        (add_le_add (hbound r r' b) (hbound r' r b)))
  rw [step0]
  have hinner : ∀ r r' : ℝ,
      (Estimates.torusIntegral fun b =>
          cubicSplitDensity 40 q a p₂ r r' b +
            cubicSplitDensity 40 q a p₂ r' r b)
        = (Estimates.torusIntegral fun b => cubicSplitDensity 40 q a p₂ r r' b) +
          (Estimates.torusIntegral fun b =>
            cubicSplitDensity 40 q a p₂ r' r b) := fun r r' =>
    cubicTorusIntegral_add
      (integrable_of_bound (cubicSplitDensity_measurable_slice 40 q a p₂ r r')
        (fun b => hbound r r' b))
      (integrable_of_bound (cubicSplitDensity_measurable_slice 40 q a p₂ r' r)
        (fun b => hbound r' r b))
  simp only [hinner]
  have hmid : ∀ r : ℝ,
      (Estimates.torusIntegral fun r' =>
          (Estimates.torusIntegral fun b => cubicSplitDensity 40 q a p₂ r r' b) +
            (Estimates.torusIntegral fun b =>
              cubicSplitDensity 40 q a p₂ r' r b))
        = (Estimates.torusIntegral fun r' =>
              Estimates.torusIntegral fun b =>
                cubicSplitDensity 40 q a p₂ r r' b) +
          (Estimates.torusIntegral fun r' =>
              Estimates.torusIntegral fun b =>
                cubicSplitDensity 40 q a p₂ r' r b) := fun r =>
    cubicTorusIntegral_add
      (integrable_of_bound (cubicSplitDensity_innerFirst_measurable 40 q a p₂ r)
        (fun r' => hinnerBound r r'))
      (integrable_of_bound (cubicSplitDensity_innerSecond_measurable 40 q a p₂ r)
        (fun r' => hinnerBound r' r))
  simp only [hmid]
  rw [cubicTorusIntegral_add
    (integrable_of_bound (cubicSplitDensity_double_measurable 40 q a p₂)
      (fun r => abs_torusIntegral_le (fun r' => hinnerBound r r')))
    (integrable_of_bound (cubicSplitDensity_doubleSwap_measurable 40 q a p₂)
      (fun r => abs_torusIntegral_le (fun r' => hinnerBound r' r)))]
  have hfirst : (Estimates.torusIntegral fun r =>
      Estimates.torusIntegral fun r' =>
        Estimates.torusIntegral fun b => cubicSplitDensity 40 q a p₂ r r' b)
      = correctionSigmaEnergy q a := by
    have hswapr : ∀ r : ℝ,
        (Estimates.torusIntegral fun r' =>
            Estimates.torusIntegral fun b =>
              cubicSplitDensity 40 q a p₂ r r' b)
          = Estimates.torusIntegral fun b =>
              Estimates.torusIntegral fun r' =>
                cubicSplitDensity 40 q a p₂ r r' b := fun r =>
      cubicTorusIntegral_swap _
        (integrable_of_bound (cubicSplitDensity_measurable_pairFirst 40 q a p₂ r)
          (fun z => hbound r z.1 z.2))
    simp only [hswapr]
    simp only [cubicSplitDensity_integral_r' hlambda hK hrho hrhopi ha hp₂]
    exact (correctionSigmaEnergy_eq_double q a).symm
  have hsecond : (Estimates.torusIntegral fun r =>
      Estimates.torusIntegral fun r' =>
        Estimates.torusIntegral fun b => cubicSplitDensity 40 q a p₂ r' r b)
      = (Estimates.torusIntegral fun r =>
          Estimates.torusIntegral fun r' =>
            Estimates.torusIntegral fun b =>
              cubicSplitDensity 40 q a p₂ r r' b) :=
    cubicTorusIntegral_swap
      (fun x y => Estimates.torusIntegral fun b =>
        cubicSplitDensity 40 q a p₂ y x b)
      (integrable_of_bound
        (cubicSplitDensity_innerPairSwap_measurable 40 q a p₂)
        (fun z => abs_torusIntegral_le (fun b => hbound z.2 z.1 b)))
  rw [hsecond, hfirst]
  ring


end RawEnergy


/-! ### Consequences for the cubic interfaces -/

/-- Discharge of the `CubicMultiplierScalarIdentification` interface for the
canonical multiplier form, namely the raw multiplier quadratic form itself. -/
theorem cubicMultiplierScalarIdentification_rawForm
    {q : Estimates.Parameters} (hlambda : 0 < q.lambda) (hK : 1 ≤ q.K)
    (hrho : 0 ≤ q.rho) (hrhopi : 3 * q.rho < Real.pi)
    {a p₂ : ℝ} (ha : 0 ≤ a) (hp₂ : |p₂| ≤ a) :
    CubicMultiplierScalarIdentification q hlambda a p₂
      (fun _ => rawCubicMultiplierEnergy q a p₂) :=
  le_of_eq (rawCubicMultiplierEnergy_eq_two_correctionSigmaEnergy
    hlambda hK hrho hrhopi ha hp₂)

/-- Proposition 4.2 now bounds the raw multiplier energy unconditionally. -/
theorem rawCubicMultiplierEnergy_le_sqrtScale
    {q : Estimates.Parameters} (hlambda : 0 < q.lambda) (hK : 1 ≤ q.K)
    (hrho : 0 ≤ q.rho) (hrhopi : 3 * q.rho < Real.pi)
    {C a p₂ : ℝ} (ha : 0 ≤ a) (hp₂ : |p₂| ≤ a)
    (hfive : Estimates.PropositionFiveTwoIntegralBound 40 C q a) :
    rawCubicMultiplierEnergy q a p₂ ≤ 2 * C * Real.sqrt (q.scaleLog a) := by
  rw [rawCubicMultiplierEnergy_eq_two_correctionSigmaEnergy
    hlambda hK hrho hrhopi ha hp₂]
  have h := correctionSigmaEnergy_le_sqrtScale hlambda hfive
  nlinarith [Real.sqrt_nonneg (q.scaleLog a)]

/-- The scalar core of Lemma 5.2 is therefore also bounded by `2 C √L`. -/
theorem rawCubicCoreEnergy_le_sqrtScale
    {q : Estimates.Parameters} (hlambda : 0 < q.lambda) (hK : 1 ≤ q.K)
    (hrho : 0 ≤ q.rho) (hrhopi : 3 * q.rho < Real.pi)
    {C a p₂ : ℝ} (ha : 0 ≤ a) (hp₂ : |p₂| ≤ a)
    (hfive : Estimates.PropositionFiveTwoIntegralBound 40 C q a) :
    rawCubicCoreEnergy q a p₂ ≤ 2 * C * Real.sqrt (q.scaleLog a) :=
  (rawCubicCoreEnergy_le_multiplier hlambda a p₂).trans
    (rawCubicMultiplierEnergy_le_sqrtScale hlambda hK hrho hrhopi ha hp₂ hfive)


/-! ### The two sectors of the scalar core -/

section Sectors

attribute [local instance] Real.fact_zero_lt_one
attribute [local instance] cubicUnitAddCircleMeasureSpace

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The degree-three `H` quadratic form of the raw correction. -/
def rawCubicHWeightEnergy (q : Estimates.Parameters) (a p₂ : ℝ) : ℝ :=
  ∫ x : UnitAddTorus (Fin 3),
    Estimates.hWeight q (rawCorrectionTotalFrequency p₂ x) *
      ‖rawCorrectionFunction 40 q a p₂ x‖ ^ 2

/-- The degree-four raising part of the scalar core of Lemma 5.2. -/
def rawCubicRaisingEnergy (q : Estimates.Parameters) (a p₂ : ℝ) : ℝ :=
  ∫ x : UnitAddTorus (Fin 3),
    8 * (Real.sin (rawCorrectionTotalFrequency p₂ x 0) ^ 2 /
          Real.sqrt (q.lambda +
            Estimates.dispersion (rawCorrectionTotalFrequency p₂ x 0)) +
        Real.sin (rawCorrectionTotalFrequency p₂ x 1) ^ 2 /
          Real.sqrt (q.lambda +
            Estimates.dispersion (rawCorrectionTotalFrequency p₂ x 1))) *
      ‖rawCorrectionFunction 40 q a p₂ x‖ ^ 2

theorem rawFrequency_zero_measurable (p₂ : ℝ) :
    Measurable fun x : UnitAddTorus (Fin 3) =>
      rawCorrectionTotalFrequency p₂ x 0 := by
  change Measurable fun x : UnitAddTorus (Fin 3) => unitTorusAngle (x 2)
  exact unitTorusAngle_measurable.comp (measurable_pi_apply 2)

theorem rawFrequency_one_measurable (p₂ : ℝ) :
    Measurable fun x : UnitAddTorus (Fin 3) =>
      rawCorrectionTotalFrequency p₂ x 1 := by
  change Measurable fun x : UnitAddTorus (Fin 3) =>
    unitTorusAngle (x 0) + unitTorusAngle (x 1) - p₂
  have hzero : Measurable (fun x : UnitAddTorus (Fin 3) =>
      unitTorusAngle (x 0)) :=
    unitTorusAngle_measurable.comp (measurable_pi_apply 0)
  have hone : Measurable (fun x : UnitAddTorus (Fin 3) =>
      unitTorusAngle (x 1)) :=
    unitTorusAngle_measurable.comp (measurable_pi_apply 1)
  exact (hzero.add hone).sub measurable_const

theorem norm_rawCorrectionFunction_sq_le {q : Estimates.Parameters}
    (hlambda : 0 < q.lambda) (a p₂ : ℝ) (x : UnitAddTorus (Fin 3)) :
    ‖rawCorrectionFunction 40 q a p₂ x‖ ^ 2 ≤
      ((40 * q.lambda)⁻¹ * (2 * q.lambda⁻¹)) ^ 2 := by
  have h := correctionCoefficient_norm_bound (kappa := 40) (q := q)
    (by norm_num) hlambda a p₂ (unitTorusAngle (x 0)) (unitTorusAngle (x 1))
    (unitTorusAngle (x 2))
  have h' : ‖rawCorrectionFunction 40 q a p₂ x‖ ≤
      (40 * q.lambda)⁻¹ * (2 * q.lambda⁻¹) := h
  have hnonneg : 0 ≤ ‖rawCorrectionFunction 40 q a p₂ x‖ := norm_nonneg _
  nlinarith [h']

theorem hWeight_le {q : Estimates.Parameters} (P : Fin 2 → ℝ) :
    Estimates.hWeight q P ≤ q.lambda + 4 := by
  unfold Estimates.hWeight Estimates.theta Estimates.dispersion
  linarith [Real.neg_one_le_cos (P 0), Real.neg_one_le_cos (P 1)]

theorem raisingFactor_le {q : Estimates.Parameters} (hlambda : 0 ≤ q.lambda)
    (P : Fin 2 → ℝ) :
    8 * (Real.sin (P 0) ^ 2 /
          Real.sqrt (q.lambda + Estimates.dispersion (P 0)) +
        Real.sin (P 1) ^ 2 /
          Real.sqrt (q.lambda + Estimates.dispersion (P 1))) ≤ 48 := by
  have h0 := Estimates.sine_sq_div_sqrt_le q.lambda (P 0) hlambda
  have h1 := Estimates.sine_sq_div_sqrt_le q.lambda (P 1) hlambda
  have hs : 2 * Real.sqrt 2 ≤ 3 := by linarith [Real.sqrt_two_lt_three_halves]
  have ha0 : |Real.sin (P 0 / 2)| ≤ 1 := Real.abs_sin_le_one _
  have ha1 : |Real.sin (P 1 / 2)| ≤ 1 := Real.abs_sin_le_one _
  have hn0 : (0:ℝ) ≤ |Real.sin (P 0 / 2)| := abs_nonneg _
  have hn1 : (0:ℝ) ≤ |Real.sin (P 1 / 2)| := abs_nonneg _
  have hp0 : 2 * Real.sqrt 2 * |Real.sin (P 0 / 2)| ≤ 3 := by nlinarith
  have hp1 : 2 * Real.sqrt 2 * |Real.sin (P 1 / 2)| ≤ 3 := by nlinarith
  linarith

theorem rawCubicHWeightIntegrand_measurable (q : Estimates.Parameters)
    (a p₂ : ℝ) :
    Measurable fun x : UnitAddTorus (Fin 3) =>
      Estimates.hWeight q (rawCorrectionTotalFrequency p₂ x) *
        ‖rawCorrectionFunction 40 q a p₂ x‖ ^ 2 := by
  have hw : Measurable fun x : UnitAddTorus (Fin 3) =>
      Estimates.hWeight q (rawCorrectionTotalFrequency p₂ x) := by
    have hzero := rawFrequency_zero_measurable p₂
    have hone := rawFrequency_one_measurable p₂
    unfold Estimates.hWeight Estimates.theta Estimates.dispersion
    fun_prop
  exact hw.mul ((rawCorrectionFunction_measurable 40 q a p₂).norm.pow_const 2)

theorem rawCubicRaisingIntegrand_measurable (q : Estimates.Parameters)
    (a p₂ : ℝ) :
    Measurable fun x : UnitAddTorus (Fin 3) =>
      8 * (Real.sin (rawCorrectionTotalFrequency p₂ x 0) ^ 2 /
            Real.sqrt (q.lambda +
              Estimates.dispersion (rawCorrectionTotalFrequency p₂ x 0)) +
          Real.sin (rawCorrectionTotalFrequency p₂ x 1) ^ 2 /
            Real.sqrt (q.lambda +
              Estimates.dispersion (rawCorrectionTotalFrequency p₂ x 1))) *
        ‖rawCorrectionFunction 40 q a p₂ x‖ ^ 2 := by
  have hw : Measurable fun x : UnitAddTorus (Fin 3) =>
      8 * (Real.sin (rawCorrectionTotalFrequency p₂ x 0) ^ 2 /
            Real.sqrt (q.lambda +
              Estimates.dispersion (rawCorrectionTotalFrequency p₂ x 0)) +
          Real.sin (rawCorrectionTotalFrequency p₂ x 1) ^ 2 /
            Real.sqrt (q.lambda +
              Estimates.dispersion (rawCorrectionTotalFrequency p₂ x 1))) := by
    have hzero := rawFrequency_zero_measurable p₂
    have hone := rawFrequency_one_measurable p₂
    unfold Estimates.dispersion
    fun_prop
  exact hw.mul ((rawCorrectionFunction_measurable 40 q a p₂).norm.pow_const 2)

theorem rawCubicHWeightEnergy_integrable {q : Estimates.Parameters}
    (hlambda : 0 < q.lambda) (a p₂ : ℝ) :
    Integrable (fun x : UnitAddTorus (Fin 3) =>
      Estimates.hWeight q (rawCorrectionTotalFrequency p₂ x) *
        ‖rawCorrectionFunction 40 q a p₂ x‖ ^ 2) volume := by
  refine integrable_of_bound (rawCubicHWeightIntegrand_measurable q a p₂)
    (C := (q.lambda + 4) * ((40 * q.lambda)⁻¹ * (2 * q.lambda⁻¹)) ^ 2)
    (fun x => ?_)
  have hw : 0 ≤ Estimates.hWeight q (rawCorrectionTotalFrequency p₂ x) :=
    (Estimates.hWeight_pos hlambda _).le
  have hwle := hWeight_le (q := q) (rawCorrectionTotalFrequency p₂ x)
  have hs := norm_rawCorrectionFunction_sq_le hlambda a p₂ x
  have hsq : (0:ℝ) ≤ ‖rawCorrectionFunction 40 q a p₂ x‖ ^ 2 := sq_nonneg _
  rw [abs_of_nonneg (mul_nonneg hw hsq)]
  exact mul_le_mul hwle hs hsq (by linarith)

theorem rawCubicRaisingEnergy_integrable {q : Estimates.Parameters}
    (hlambda : 0 < q.lambda) (a p₂ : ℝ) :
    Integrable (fun x : UnitAddTorus (Fin 3) =>
      8 * (Real.sin (rawCorrectionTotalFrequency p₂ x 0) ^ 2 /
            Real.sqrt (q.lambda +
              Estimates.dispersion (rawCorrectionTotalFrequency p₂ x 0)) +
          Real.sin (rawCorrectionTotalFrequency p₂ x 1) ^ 2 /
            Real.sqrt (q.lambda +
              Estimates.dispersion (rawCorrectionTotalFrequency p₂ x 1))) *
        ‖rawCorrectionFunction 40 q a p₂ x‖ ^ 2) volume := by
  refine integrable_of_bound (rawCubicRaisingIntegrand_measurable q a p₂)
    (C := 48 * ((40 * q.lambda)⁻¹ * (2 * q.lambda⁻¹)) ^ 2) (fun x => ?_)
  have hfac : 0 ≤ 8 * (Real.sin (rawCorrectionTotalFrequency p₂ x 0) ^ 2 /
        Real.sqrt (q.lambda +
          Estimates.dispersion (rawCorrectionTotalFrequency p₂ x 0)) +
      Real.sin (rawCorrectionTotalFrequency p₂ x 1) ^ 2 /
        Real.sqrt (q.lambda +
          Estimates.dispersion (rawCorrectionTotalFrequency p₂ x 1))) := by
    have h0 : (0:ℝ) ≤ Real.sin (rawCorrectionTotalFrequency p₂ x 0) ^ 2 /
        Real.sqrt (q.lambda +
          Estimates.dispersion (rawCorrectionTotalFrequency p₂ x 0)) :=
      div_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)
    have h1 : (0:ℝ) ≤ Real.sin (rawCorrectionTotalFrequency p₂ x 1) ^ 2 /
        Real.sqrt (q.lambda +
          Estimates.dispersion (rawCorrectionTotalFrequency p₂ x 1)) :=
      div_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)
    linarith
  have hfacle := raisingFactor_le (q := q) hlambda.le
    (rawCorrectionTotalFrequency p₂ x)
  have hs := norm_rawCorrectionFunction_sq_le hlambda a p₂ x
  have hsq : (0:ℝ) ≤ ‖rawCorrectionFunction 40 q a p₂ x‖ ^ 2 := sq_nonneg _
  rw [abs_of_nonneg (mul_nonneg hfac hsq)]
  exact mul_le_mul hfacle hs hsq (by norm_num)

/-- The scalar core of Lemma 5.2 splits into the `H₃` quadratic form and the
degree-four raising term. -/
theorem rawCubicCoreEnergy_eq_add {q : Estimates.Parameters}
    (hlambda : 0 < q.lambda) (a p₂ : ℝ) :
    rawCubicCoreEnergy q a p₂ =
      rawCubicHWeightEnergy q a p₂ + rawCubicRaisingEnergy q a p₂ := by
  unfold rawCubicCoreEnergy rawCubicHWeightEnergy rawCubicRaisingEnergy
  rw [← integral_add (rawCubicHWeightEnergy_integrable hlambda a p₂)
    (rawCubicRaisingEnergy_integrable hlambda a p₂)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  unfold Estimates.fourEstimateCore
  ring


end Sectors

/-! ### Reduction of the cubic intertwining interface to the two modules -/

/-- Cross-module statement of the `H₃` half of Lemma 5.2: the degree-three
`H` quadratic form of the projected correction is at most the raw `H`-weight
energy. This is (Hsym) together with the contractivity (46) of the
coincident-row projection for the positive multiplier `λ+θ(P)`
(`manuscript.tex:1233-1235`, `manuscript.tex:1257-1272`). -/
def ConcreteHThreeQuadraticBound (q : Estimates.Parameters)
    (hlambda : 0 < q.lambda) (a p₁ p₂ : ℝ) (hThree : WalshL2 → ℝ) : Prop :=
  hThree (shiftedCorrectionWalsh (kappa := 40) (by norm_num) hlambda a p₁ p₂) ≤
    rawCubicHWeightEnergy q a p₂

/-- Cross-module statement of the `D₃` half of Lemma 5.2: the `H⁻¹` energy of
the degree-four raising of the projected correction is at most the raw
degree-four raising energy. This is the raising formula (45), the four-term
Cauchy--Schwarz, the line integral (22), and (46)
(`manuscript.tex:1257-1272`). -/
def ConcreteDThreeRaisingBound (q : Estimates.Parameters)
    (hlambda : 0 < q.lambda) (a p₁ p₂ : ℝ) (dFour : WalshL2 → ℝ) : Prop :=
  dFour (shiftedCorrectionWalsh (kappa := 40) (by norm_num) hlambda a p₁ p₂) ≤
    rawCubicRaisingEnergy q a p₂

/-- The scalar core of Lemma 5.2 for the competitor's phase-twisted
coefficient, from the two sector bounds. -/
theorem shiftedCorrectionWalsh_cubicCoreEnergy_le_of_sectors
    {q : Estimates.Parameters} (hlambda : 0 < q.lambda) {a p₁ p₂ : ℝ}
    (hThree dFour : WalshL2 → ℝ)
    (hH : ConcreteHThreeQuadraticBound q hlambda a p₁ p₂ hThree)
    (hD : ConcreteDThreeRaisingBound q hlambda a p₁ p₂ dFour) :
    let k := shiftedCorrectionWalsh (kappa := 40) (by norm_num) hlambda a p₁ p₂
    hThree k + dFour k ≤ rawCubicCoreEnergy q a p₂ := by
  dsimp
  rw [rawCubicCoreEnergy_eq_add hlambda a p₂]
  exact add_le_add hH hD

/-- Lemma 5.2 and Proposition 4.2 in the concrete model. The only remaining
premises are the two operator-sector bounds; the multiplier identification is
now proved. -/
theorem correctionWalsh_cubicEnergy_le_sqrtScale_of_sectors
    {q : Estimates.Parameters} (hlambda : 0 < q.lambda) (hK : 1 ≤ q.K)
    (hrho : 0 ≤ q.rho) (hrhopi : 3 * q.rho < Real.pi)
    {C a p₁ p₂ : ℝ} (ha : 0 ≤ a) (hp₂ : |p₂| ≤ a)
    (hThree dFour : WalshL2 → ℝ)
    (hH : ConcreteHThreeQuadraticBound q hlambda a p₁ p₂ hThree)
    (hD : ConcreteDThreeRaisingBound q hlambda a p₁ p₂ dFour)
    (hfive : Estimates.PropositionFiveTwoIntegralBound 40 C q a) :
    let k := shiftedCorrectionWalsh (kappa := 40) (by norm_num) hlambda a p₁ p₂
    hThree k + dFour k ≤ 2 * C * Real.sqrt (q.scaleLog a) := by
  dsimp
  exact (shiftedCorrectionWalsh_cubicCoreEnergy_le_of_sectors hlambda hThree
      dFour hH hD).trans
    ((rawCubicCoreEnergy_le_multiplier hlambda a p₂).trans
      (rawCubicMultiplierEnergy_le_sqrtScale hlambda hK hrho hrhopi ha hp₂ hfive))

end

end Manhattan.Glue
