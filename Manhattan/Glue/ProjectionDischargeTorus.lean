import Manhattan.Estimates.Elementary
import Manhattan.Estimates.RankOne
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Normalized torus calculus for the projection-error discharge

The declarations here are the elementary integral facts used to discharge the
two open interfaces of `Manhattan.Glue.ProjectionError`: translation
invariance of the normalized Haar integral, its Fubini exchange, the
character orthogonality that makes `Pi_2` annihilate a coincident-row
coefficient, and the Jensen inequality behind the weighted contractivity.

All integrals use `Manhattan.Estimates.torusIntegral`, the normalized Haar
integral on `(-pi, pi]`.

Paper: `manuscript.tex:806-819` and `manuscript.tex:1274-1303`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Manhattan.Glue

noncomputable section

open Estimates (torus torusIntegral)

/-- The chosen fundamental domain has Lebesgue measure `2 pi`. -/
theorem volume_torus : volume Estimates.torus = ENNReal.ofReal (2 * Real.pi) := by
  rw [Estimates.torus, Real.volume_Ioc]
  congr 1
  ring

theorem volume_torus_ne_top' : volume Estimates.torus ≠ ⊤ := by
  rw [volume_torus]
  exact ENNReal.ofReal_ne_top

instance isFiniteMeasure_restrict_torus :
    IsFiniteMeasure (volume.restrict Estimates.torus) :=
  ⟨by
    rw [Measure.restrict_apply_univ]
    exact lt_of_le_of_ne le_top volume_torus_ne_top'⟩

/-- The normalized integral of a constant. -/
@[simp] theorem torusIntegral_const {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (c : E) :
    torusIntegral (fun _ : ℝ => c) = c := by
  rw [Estimates.torusIntegral, setIntegral_const, measureReal_def, volume_torus,
    ENNReal.toReal_ofReal (by positivity), smul_smul,
    inv_mul_cancel₀ (by positivity), one_smul]

theorem torusIntegral_add {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f g : ℝ → E}
    (hf : Integrable f (volume.restrict Estimates.torus))
    (hg : Integrable g (volume.restrict Estimates.torus)) :
    torusIntegral (fun x => f x + g x) = torusIntegral f + torusIntegral g := by
  rw [Estimates.torusIntegral, Estimates.torusIntegral, Estimates.torusIntegral,
    integral_add hf hg, smul_add]

theorem torusIntegral_sub {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f g : ℝ → E}
    (hf : Integrable f (volume.restrict Estimates.torus))
    (hg : Integrable g (volume.restrict Estimates.torus)) :
    torusIntegral (fun x => f x - g x) = torusIntegral f - torusIntegral g := by
  rw [Estimates.torusIntegral, Estimates.torusIntegral, Estimates.torusIntegral,
    integral_sub hf hg, smul_sub]

theorem torusIntegral_const_mul (c : ℂ) (f : ℝ → ℂ) :
    torusIntegral (fun x => c * f x) = c * torusIntegral f := by
  simp only [Estimates.torusIntegral, integral_const_mul, Complex.real_smul]
  ring

theorem torusIntegral_real_const_mul (c : ℝ) (f : ℝ → ℝ) :
    torusIntegral (fun x => c * f x) = c * torusIntegral f := by
  simp only [Estimates.torusIntegral, integral_const_mul, smul_eq_mul]
  ring

theorem torusIntegral_mul_const (c : ℂ) (f : ℝ → ℂ) :
    torusIntegral (fun x => f x * c) = torusIntegral f * c := by
  simp only [Estimates.torusIntegral, integral_mul_const, Complex.real_smul]
  ring

theorem torusIntegral_nonneg {f : ℝ → ℝ} (hf : ∀ x, 0 ≤ f x) :
    0 ≤ torusIntegral f := by
  rw [Estimates.torusIntegral, smul_eq_mul]
  exact mul_nonneg (by positivity) (integral_nonneg fun x => hf x)

theorem torusIntegral_mono {f g : ℝ → ℝ}
    (hf : Integrable f (volume.restrict Estimates.torus))
    (hg : Integrable g (volume.restrict Estimates.torus))
    (hfg : ∀ x, f x ≤ g x) :
    torusIntegral f ≤ torusIntegral g := by
  rw [Estimates.torusIntegral, Estimates.torusIntegral]
  simp only [smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (integral_mono hf hg hfg) (by positivity)

/-- Translation invariance of the normalized Haar integral. -/
theorem torusIntegral_comp_add_right {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f : ℝ → E}
    (hf : Function.Periodic f (2 * Real.pi)) (c : ℝ) :
    torusIntegral (fun x : ℝ => f (x + c)) = torusIntegral f := by
  have hpi : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  rw [Estimates.torusIntegral, Estimates.torusIntegral, Estimates.torus,
    ← intervalIntegral.integral_of_le hpi,
    ← intervalIntegral.integral_of_le hpi,
    intervalIntegral.integral_comp_add_right]
  congr 1
  have hperiod := hf.intervalIntegral_add_eq (-Real.pi + c) (-Real.pi)
  convert hperiod using 2 <;> ring

/-- Bounded measurable functions are integrable on the fundamental domain. -/
theorem integrable_torus_of_bound {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} {C : ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict Estimates.torus))
    (hC : ∀ x, ‖f x‖ ≤ C) :
    Integrable f (volume.restrict Estimates.torus) :=
  Integrable.mono' (integrableOn_const (C := C) volume_torus_ne_top') hf
    (Filter.Eventually.of_forall hC)

/-- The normalized integral of a bounded function obeys the same bound. -/
theorem norm_torusIntegral_le_of_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f : ℝ → E} {C : ℝ}
    (hC : ∀ x, ‖f x‖ ≤ C) :
    ‖torusIntegral f‖ ≤ C := by
  have hCnonneg : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
  have hbound :
      ‖∫ x in Estimates.torus, f x‖ ≤ C * (volume Estimates.torus).toReal := by
    simpa [measureReal_def] using
      norm_setIntegral_le_of_norm_le_const (f := f) (s := Estimates.torus)
        (μ := volume) (C := C)
        (lt_of_le_of_ne le_top volume_torus_ne_top')
        (fun x _ => hC x)
  rw [Estimates.torusIntegral, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 * Real.pi)⁻¹)]
  rw [volume_torus, ENNReal.toReal_ofReal (by positivity)] at hbound
  calc
    (2 * Real.pi)⁻¹ * ‖∫ x in Estimates.torus, f x‖ ≤
        (2 * Real.pi)⁻¹ * (C * (2 * Real.pi)) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = C := by
      field_simp

/-- Jensen's inequality for the normalized Haar integral of a bounded
measurable function. -/
theorem norm_torusIntegral_sq_le_of_bound {f : ℝ → ℂ} {C : ℝ}
    (hf : Measurable f) (hC : ∀ x, ‖f x‖ ≤ C) :
    ‖torusIntegral f‖ ^ 2 ≤ torusIntegral (fun x => ‖f x‖ ^ 2) := by
  have hCnonneg : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
  have htwopi : (0 : ℝ) < 2 * Real.pi := by positivity
  set μ := volume.restrict Estimates.torus with hμ
  have hnorm : Measurable fun x => ‖f x‖ := hf.norm
  have hone : MemLp (fun _ : ℝ => (1 : ℝ)) (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using
      (memLp_const (μ := μ) (p := (2 : ℝ≥0∞)) (1 : ℝ))
  have hgmem : MemLp (fun x => ‖f x‖) (ENNReal.ofReal (2 : ℝ)) μ := by
    have : MemLp (fun x => ‖f x‖) 2 μ :=
      MemLp.of_bound hnorm.aestronglyMeasurable C
        (Filter.Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
          exact hC x)
    simpa using this
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall fun _ : ℝ => zero_le_one)
    (Filter.Eventually.of_forall fun x : ℝ => norm_nonneg (f x))
    hone hgmem
  simp_rw [Real.rpow_two, one_mul, one_pow] at hholder
  rw [integral_const] at hholder
  norm_num [← Real.sqrt_eq_rpow] at hholder
  have hmeasure : (μ Set.univ).toReal = 2 * Real.pi := by
    rw [hμ, Measure.restrict_apply_univ, volume_torus,
      ENNReal.toReal_ofReal (by positivity)]
  rw [measureReal_def, hmeasure] at hholder
  have hsqNonneg : 0 ≤ ∫ x, ‖f x‖ ^ 2 ∂μ :=
    integral_nonneg fun x => sq_nonneg _
  have hint : Integrable f μ :=
    integrable_torus_of_bound hf.aestronglyMeasurable hC
  have hstep1 : ‖∫ x, f x ∂μ‖ ≤ ∫ x, ‖f x‖ ∂μ :=
    norm_integral_le_integral_norm f
  have hstep2 : ‖∫ x, f x ∂μ‖ ≤
      Real.sqrt (2 * Real.pi) * Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂μ) :=
    hstep1.trans hholder
  have hsq := (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).2 hstep2
  rw [mul_pow, Real.sq_sqrt htwopi.le, Real.sq_sqrt hsqNonneg] at hsq
  rw [Estimates.torusIntegral, Estimates.torusIntegral]
  simp only [smul_eq_mul]
  rw [show ‖(2 * Real.pi : ℝ)⁻¹ • ∫ x in Estimates.torus, f x‖ ^ 2 =
      ((2 * Real.pi)⁻¹) ^ 2 * ‖∫ x in Estimates.torus, f x‖ ^ 2 by
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 * Real.pi)⁻¹), mul_pow]]
  calc
    ((2 * Real.pi)⁻¹) ^ 2 * ‖∫ x in Estimates.torus, f x‖ ^ 2 ≤
        ((2 * Real.pi)⁻¹) ^ 2 * (2 * Real.pi * ∫ x in Estimates.torus, ‖f x‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = (2 * Real.pi)⁻¹ * ∫ x in Estimates.torus, ‖f x‖ ^ 2 := by
      field_simp

/-- Character orthogonality on the normalized torus. -/
theorem torusIntegral_intCharacter (m : ℤ) :
    torusIntegral (fun x : ℝ =>
        Complex.exp (Complex.I * (((m : ℝ) * x : ℝ) : ℂ))) =
      if m = 0 then 1 else 0 := by
  have hpi : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  by_cases hm : m = 0
  · subst m
    simp
  · rw [if_neg hm, Estimates.torusIntegral, Estimates.torus,
      ← intervalIntegral.integral_of_le hpi]
    have hc : Complex.I * (m : ℂ) ≠ 0 :=
      mul_ne_zero Complex.I_ne_zero (Int.cast_ne_zero.mpr hm)
    have hintegrand :
        (fun x : ℝ => Complex.exp (Complex.I * (((m : ℝ) * x : ℝ) : ℂ))) =
          fun x : ℝ => Complex.exp ((Complex.I * (m : ℂ)) * x) := by
      funext x
      congr 1
      push_cast
      ring
    rw [hintegrand, integral_exp_mul_complex hc,
      show ((-Real.pi : ℝ) : ℂ) = -(Real.pi : ℂ) by norm_num]
    have hperiod :
        Complex.exp ((Complex.I * (m : ℂ)) * (Real.pi : ℂ)) =
          Complex.exp ((Complex.I * (m : ℂ)) * (-(Real.pi : ℂ))) := by
      calc
        Complex.exp ((Complex.I * (m : ℂ)) * (Real.pi : ℂ)) =
            Complex.exp ((Complex.I * (m : ℂ)) * (-(Real.pi : ℂ)) +
              (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) := by
              congr 1
              ring
        _ = Complex.exp ((Complex.I * (m : ℂ)) * (-(Real.pi : ℂ))) *
              Complex.exp ((m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) :=
            Complex.exp_add _ _
        _ = Complex.exp ((Complex.I * (m : ℂ)) * (-(Real.pi : ℂ))) := by
            rw [Complex.exp_int_mul_two_pi_mul_I]
            simp
    rw [hperiod, sub_self, zero_div, smul_zero]

/-- Parametric normalized torus integrals of a jointly measurable function are
measurable. -/
theorem stronglyMeasurable_torusIntegral {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {F : X × ℝ → E}
    (hF : StronglyMeasurable F) :
    StronglyMeasurable fun x : X => torusIntegral (fun y => F (x, y)) := by
  have h := hF.integral_prod_right' (ν := volume.restrict Estimates.torus)
  simpa only [Estimates.torusIntegral] using h.const_smul ((2 * Real.pi)⁻¹)

/-- Bounded measurable functions are integrable for the product of two copies
of the fundamental domain. -/
theorem integrable_prod_torus_of_bound {E : Type*} [NormedAddCommGroup E]
    {F : ℝ × ℝ → E} {C : ℝ}
    (hF : AEStronglyMeasurable F
      ((volume.restrict Estimates.torus).prod (volume.restrict Estimates.torus)))
    (hC : ∀ z, ‖F z‖ ≤ C) :
    Integrable F
      ((volume.restrict Estimates.torus).prod (volume.restrict Estimates.torus)) :=
  Integrable.mono' (integrable_const C) hF (Filter.Eventually.of_forall hC)

/-- Fubini exchange for the normalized torus. -/
theorem torusIntegral_swap {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {F : ℝ → ℝ → E}
    (hF : Integrable (Function.uncurry F)
      ((volume.restrict Estimates.torus).prod (volume.restrict Estimates.torus))) :
    torusIntegral (fun x : ℝ => torusIntegral (fun y : ℝ => F x y)) =
      torusIntegral (fun y : ℝ => torusIntegral (fun x : ℝ => F x y)) := by
  simp only [Estimates.torusIntegral, integral_smul]
  rw [integral_integral_swap hF]

/-- The one-dimensional symbol is `2 pi`-periodic. -/
theorem dispersion_periodic :
    Function.Periodic Estimates.dispersion (2 * Real.pi) := by
  intro x
  unfold Estimates.dispersion
  rw [Real.cos_add_two_pi]

/-- The paper's multiplier is `2 pi`-periodic in the row frequency. -/
theorem multiplier_periodic (kappa : ℝ) (q : Estimates.Parameters) (beta : ℝ) :
    Function.Periodic (fun alpha : ℝ =>
      Estimates.multiplier kappa q
        (Estimates.mixedTotalFrequency beta alpha)) (2 * Real.pi) := by
  intro alpha
  unfold Estimates.multiplier Estimates.theta Estimates.mixedTotalFrequency
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [dispersion_periodic alpha]
  congr 2
  rw [show (alpha + 2 * Real.pi) / 2 = alpha / 2 + Real.pi by ring,
    Real.sin_add_pi, abs_neg]

/-- A uniform bound for the multiplier. -/
theorem multiplier_le {kappa : ℝ} {q : Estimates.Parameters}
    (hkappa : 0 ≤ kappa) (P : Fin 2 → ℝ) :
    Estimates.multiplier kappa q P ≤ kappa * (q.lambda + 8) := by
  unfold Estimates.multiplier Estimates.theta Estimates.dispersion
  apply mul_le_mul_of_nonneg_left _ hkappa
  have h0 := Real.neg_one_le_cos (P 0)
  have h1 := Real.neg_one_le_cos (P 1)
  have hs0 := Real.abs_sin_le_one (P 0 / 2)
  have hs1 := Real.abs_sin_le_one (P 1 / 2)
  linarith

end

end Manhattan.Glue
