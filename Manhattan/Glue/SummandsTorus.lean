import Manhattan.Walsh.LowDegree
import Manhattan.Estimates.Elementary

/-!
# Torus bookkeeping for the four summands of (22)

This file collects the elementary facts about the paper's
normalized torus `(-π,π]` and about Mathlib's `AddCircle torusPeriod`
that the summand estimates need, together with the two dispersion
inequalities used to move a frequency shift through `d(s)=1-\cos s`.

The change of variables `∫ · d(haar) = torusIntegral ·` is the fact named
as missing, item 1, in the degree-one
case (period `2π`, no rescaling of the frequency variable).

Paper: `manuscript.tex:743-758` and `manuscript.tex:791-800`.
-/

noncomputable section

open MeasureTheory Set
open scoped ComplexConjugate

namespace Manhattan.Glue

/-- Mathlib's normalized Haar measure on the paper's frequency torus. -/
abbrev haarTorus : Measure (AddCircle torusPeriod) := AddCircle.haarAddCircle

/-- Integration against normalized Haar measure on `AddCircle torusPeriod`
is the paper's `torusIntegral` of the pullback to `(-π,π]`. -/
theorem integral_haarTorus_eq_torusIntegral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (g : AddCircle torusPeriod → E) :
    ∫ x, g x ∂haarTorus =
      Manhattan.Estimates.torusIntegral fun r : ℝ => g (r : AddCircle torusPeriod) := by
  have hend : -Real.pi + torusPeriod = Real.pi := by
    rw [torusPeriod]; ring
  rw [AddCircle.integral_haarAddCircle,
    ← AddCircle.integral_preimage torusPeriod (-Real.pi) g, hend]
  simp only [Manhattan.Estimates.torusIntegral, Manhattan.Estimates.torus, torusPeriod]

/-- `d(s+t) ≤ 2d(s)+2d(t)`: a frequency shift costs a universal factor. -/
theorem dispersion_add_le (s t : ℝ) :
    Manhattan.Estimates.dispersion (s + t) ≤
      2 * Manhattan.Estimates.dispersion s + 2 * Manhattan.Estimates.dispersion t := by
  simp only [Manhattan.Estimates.dispersion, Real.cos_add]
  nlinarith [Real.sin_sq_add_cos_sq s, Real.sin_sq_add_cos_sq t,
    sq_nonneg (Real.cos s + Real.cos t - 2), sq_nonneg (Real.sin s - Real.sin t)]

/-- `d` is monotone in `|·|` on the torus. -/
theorem dispersion_le_of_abs_le {s t : ℝ} (hs : |s| ≤ Real.pi) (h : |t| ≤ |s|) :
    Manhattan.Estimates.dispersion t ≤ Manhattan.Estimates.dispersion s := by
  have hcos : Real.cos |s| ≤ Real.cos |t| :=
    Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg t) hs h
  simp only [Manhattan.Estimates.dispersion]
  rw [← Real.cos_abs s, ← Real.cos_abs t]
  linarith

/-- Multiplication by the character `fourier n` preserves `L²`. -/
theorem memLp_fourier_mul (n : ℤ) (F : Lp ℂ 2 haarTorus) :
    MemLp (fun x : AddCircle torusPeriod => fourier n x * F x) 2 haarTorus := by
  refine (Lp.memLp F).mono ?_ ?_
  · exact ((map_continuous (fourier n)).aestronglyMeasurable).mul
      (Lp.aestronglyMeasurable F)
  · filter_upwards with x
    have hone : ‖fourier n x‖ = 1 := Circle.norm_coe _
    rw [norm_mul, hone, one_mul]

/-- The `L²` vector `fourier n · F`. -/
noncomputable def fourierMul (n : ℤ) (F : Lp ℂ 2 haarTorus) : Lp ℂ 2 haarTorus :=
  (memLp_fourier_mul n F).toLp _

theorem coeFn_fourierMul (n : ℤ) (F : Lp ℂ 2 haarTorus) :
    (fourierMul n F : AddCircle torusPeriod → ℂ) =ᵐ[haarTorus]
      fun x => fourier n x * F x :=
  MemLp.coeFn_toLp _

/-- Multiplying by `fourier n` shifts the Fourier coefficients by `n`. -/
theorem repr_fourierMul (n : ℤ) (F : Lp ℂ 2 haarTorus) (k : ℤ) :
    fourierBasis.repr (fourierMul n F) k = fourierBasis.repr F (k - n) := by
  rw [fourierBasis_repr, fourierBasis_repr, fourierCoeff, fourierCoeff]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_fourierMul n F] with x hx
  rw [hx, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← fourier_add,
    show -k + n = -(k - n) by ring]

/-- The quadratic form of the character multiplication. -/
theorem inner_fourierMul_self (n : ℤ) (F : Lp ℂ 2 haarTorus) :
    (inner ℂ F (fourierMul n F) : ℂ) =
      ∫ x, fourier n x * ((‖F x‖ ^ 2 : ℝ) : ℂ) ∂haarTorus := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_fourierMul n F] with x hx
  rw [hx, RCLike.inner_apply, mul_assoc, RCLike.mul_conj, Complex.ofReal_pow]
  rfl

/-- The `L²` norm of an `Lp` vector as an integral of the squared pointwise
norm. Stated for a general measure; used on the frequency torus of every
degree. -/
theorem integral_norm_sq_lp {α : Type*} [MeasurableSpace α] {mu : Measure α}
    (F : Lp ℂ 2 mu) : ∫ x, ‖(F : α → ℂ) x‖ ^ 2 ∂mu = ‖F‖ ^ 2 := by
  have h1 : (inner ℂ F F : ℂ) = ∫ x, ((‖(F : α → ℂ) x‖ ^ 2 : ℝ) : ℂ) ∂mu := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [RCLike.inner_apply, RCLike.mul_conj]
    norm_cast
  have h2 : (inner ℂ F F : ℂ) = ((‖F‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [h2, integral_complex_ofReal] at h1
  exact_mod_cast h1.symm

end Manhattan.Glue
