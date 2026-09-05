import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Elementary torus estimates

This file defines the real-frequency vocabulary used in Sections 4--5 and
proves the quadratic comparison (21). The endpoint convention for the torus
is `(-π, π]`; endpoints are immaterial for the normalized integral.

Paper: `manuscript.tex:743-757`, `manuscript.tex:860-883`.
-/

open MeasureTheory Set

namespace Manhattan.Estimates

noncomputable section

/-- The chosen real fundamental domain for the one-dimensional torus. -/
def torus : Set ℝ := Set.Ioc (-Real.pi) Real.pi

/-- Normalized Haar integration on `𝕋 = (-π, π]`, represented using Lebesgue measure. -/
noncomputable def torusIntegral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : ℝ → E) : E :=
  (2 * Real.pi)⁻¹ • ∫ r in torus, f r

/-- The one-dimensional symbol `d(s) = 1 - cos s`. -/
def dispersion (s : ℝ) : ℝ := 1 - Real.cos s

/-- The two-dimensional symbol `θ(P) = d(P₁) + d(P₂)`. -/
def theta (P : Fin 2 → ℝ) : ℝ := dispersion (P 0) + dispersion (P 1)

/-- The positive part of the logarithm used throughout the estimates. -/
def logPos (x : ℝ) : ℝ := max 0 (Real.log x)

/-- The fixed parameters of the explicit competitor construction. -/
structure Parameters where
  lambda : ℝ
  K : ℝ
  rho : ℝ

/-- The parameter range fixed at the start of Section 4. -/
def Parameters.Admissible (q : Parameters) : Prop :=
  0 < q.lambda ∧ q.lambda ≤ 1 ∧ 20 ≤ q.K ∧ 0 < q.rho ∧ q.rho ≤ Real.pi / 20

/-- The small fixed frequency cutoff `r₀ = ρ/(100K)`. -/
def Parameters.r0 (q : Parameters) : ℝ := q.rho / (100 * q.K)

/-- The scale `δ = √λ + a`. -/
noncomputable def Parameters.delta (q : Parameters) (a : ℝ) : ℝ :=
  Real.sqrt q.lambda + a

/-- The logarithmic scale `L = 1 + log₊(r₀/δ)`. -/
noncomputable def Parameters.scaleLog (q : Parameters) (a : ℝ) : ℝ :=
  1 + logPos (q.r0 / q.delta a)

/-- The support interval `I = [Kδ,r₀]`. -/
noncomputable def Parameters.supportInterval (q : Parameters) (a : ℝ) : Set ℝ :=
  Set.Icc (q.K * q.delta a) q.r0

/-- The lower threshold `L_* = 2 log K + 3` in Lemma 4.1. -/
noncomputable def Parameters.logThreshold (q : Parameters) : ℝ :=
  2 * Real.log q.K + 3

/-- The resolvent weight from (Hsym) for a total frequency `P`. -/
def hWeight (q : Parameters) (P : Fin 2 → ℝ) : ℝ := q.lambda + theta P

/-- The mixed degree-two `H⁻¹` weight at frequencies `(β,r)`. -/
def mixedHMinusWeight (q : Parameters) (r beta : ℝ) : ℝ :=
  (q.lambda + dispersion r + dispersion beta)⁻¹

/-- The two-row degree-two `H⁻¹` weight at total frequency `(p₁,α)`. -/
def twoRowHMinusWeight (q : Parameters) (p₁ alpha : ℝ) : ℝ :=
  (q.lambda + dispersion p₁ + dispersion alpha)⁻¹

/-- `d` is nonnegative. -/
theorem dispersion_nonneg (s : ℝ) : 0 ≤ dispersion s := by
  exact sub_nonneg.mpr (Real.cos_le_one s)

/-- Equation (21): the sharp elementary quadratic comparison on `[-π,π]`. -/
theorem dispersion_quadratic_bounds {s : ℝ} (hs : |s| ≤ Real.pi) :
    2 * s ^ 2 / Real.pi ^ 2 ≤ dispersion s ∧ dispersion s ≤ s ^ 2 / 2 := by
  constructor
  · have hcos := Real.cos_le_one_sub_mul_cos_sq hs
    have h := sub_le_sub_left hcos 1
    convert h using 1
    all_goals ring
  · have hcos := Real.one_sub_sq_div_two_le_cos (x := s)
    dsimp [dispersion]
    linarith

/-- A convenient consequence of (21), with the upper bound written multiplicatively. -/
theorem dispersion_le_half_mul_sq (s : ℝ) : dispersion s ≤ (1 / 2 : ℝ) * s ^ 2 := by
  have hcos := Real.one_sub_sq_div_two_le_cos (x := s)
  dsimp [dispersion]
  linarith

/-- `θ` is nonnegative. -/
theorem theta_nonneg (P : Fin 2 → ℝ) : 0 ≤ theta P := by
  exact add_nonneg (dispersion_nonneg _) (dispersion_nonneg _)

/-- Every resolvent multiplier is positive when `λ > 0`. -/
theorem hWeight_pos {q : Parameters} (hlam : 0 < q.lambda) (P : Fin 2 → ℝ) :
    0 < hWeight q P := by
  exact add_pos_of_pos_of_nonneg hlam (theta_nonneg P)

/-- Every mixed `H⁻¹` denominator is positive when `λ > 0`. -/
theorem mixed_denominator_pos {q : Parameters} (hlam : 0 < q.lambda) (r beta : ℝ) :
    0 < q.lambda + dispersion r + dispersion beta := by
  exact add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg hlam (dispersion_nonneg r))
    (dispersion_nonneg beta)

/-- The normalized torus integral of the constant function is one. -/
theorem torusIntegral_one : torusIntegral (fun _ : ℝ => (1 : ℝ)) = 1 := by
  simp [torusIntegral, torus]
  rw [max_eq_left]
  · calc
      Real.pi⁻¹ * 2⁻¹ * (Real.pi + Real.pi) = Real.pi * Real.pi⁻¹ := by ring
      _ = 1 := mul_inv_cancel₀ Real.pi_ne_zero
  · positivity

private theorem logScaleAntiderivative_hasDerivAt {b x : ℝ} (hx : 0 < x) (hxb : x ≤ b) :
    HasDerivAt (fun y : ℝ => -2 * Real.sqrt (1 + Real.log b - Real.log y))
      (1 / (x * Real.sqrt (1 + Real.log b - Real.log x))) x := by
  have hlog : Real.log x ≤ Real.log b := Real.log_le_log hx hxb
  have hinner : 0 < 1 + Real.log b - Real.log x := by linarith
  have hderiv : HasDerivAt (fun y : ℝ => 1 + Real.log b - Real.log y) (-1 / x) x := by
    convert (hasDerivAt_const x (1 + Real.log b)).sub (Real.hasDerivAt_log hx.ne') using 1
    all_goals ring
  have hsqrt := hderiv.sqrt hinner.ne'
  convert hsqrt.const_mul (-2) using 1
  field_simp

/-- The exact `u = log(r₀/r)` integral used in Step 3 of Proposition 4.2. -/
theorem logScaleIntegral {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ r in a..b, (r * Real.sqrt (1 + Real.log (b / r)))⁻¹) =
      2 * (Real.sqrt (1 + Real.log (b / a)) - 1) := by
  have hb : 0 < b := ha.trans_le hab
  have hderiv : ∀ x ∈ Set.Icc a b,
      HasDerivAt (fun y : ℝ => -2 * Real.sqrt (1 + Real.log b - Real.log y))
        ((x * Real.sqrt (1 + Real.log (b / x)))⁻¹) x := by
    intro x hx
    have hxpos : 0 < x := ha.trans_le hx.1
    simpa only [one_div, Real.log_div hb.ne' hxpos.ne', sub_eq_add_neg, add_assoc] using
      logScaleAntiderivative_hasDerivAt hxpos hx.2
  have hderiv' : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun y : ℝ => -2 * Real.sqrt (1 + Real.log b - Real.log y))
        ((x * Real.sqrt (1 + Real.log (b / x)))⁻¹) x := by
    simpa [Set.uIcc_of_le hab] using hderiv
  have hint : IntervalIntegrable (fun x : ℝ =>
      (x * Real.sqrt (1 + Real.log (b / x)))⁻¹) MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    have hxIcc : x ∈ Set.Icc a b := by simpa [Set.uIcc_of_le hab] using hx
    have hxpos : 0 < x := ha.trans_le hxIcc.1
    have hlog : Real.log x ≤ Real.log b := Real.log_le_log hxpos hxIcc.2
    have hinner : 0 < 1 + Real.log (b / x) := by
      rw [Real.log_div hb.ne' hxpos.ne']
      linarith
    have hxne : x ≠ 0 := hxpos.ne'
    have hbne : b ≠ 0 := hb.ne'
    have hdivne : b / x ≠ 0 := div_ne_zero hbne hxne
    have hsqrtne : Real.sqrt (1 + Real.log (b / x)) ≠ 0 :=
      (Real.sqrt_pos.2 hinner).ne'
    have hprodne : x * Real.sqrt (1 + Real.log (b / x)) ≠ 0 :=
      mul_ne_zero hxne hsqrtne
    apply ContinuousAt.continuousWithinAt
    have hcdiv : ContinuousAt (fun y : ℝ => b / y) x :=
      continuousAt_const.div continuousAt_id hxne
    have hclog : ContinuousAt (fun y : ℝ => Real.log (b / y)) x :=
      hcdiv.log hdivne
    exact (continuousAt_id.mul (continuousAt_const.add hclog).sqrt).inv₀ hprodne
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv' hint]
  rw [show 1 + Real.log b - Real.log b = 1 by ring, Real.sqrt_one,
    Real.log_div hb.ne' ha.ne']
  ring_nf

/-- The upper bound `≤ 2√L` extracted from the exact logarithmic integral. -/
theorem logScaleIntegral_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ r in a..b, (r * Real.sqrt (1 + Real.log (b / r)))⁻¹) ≤
      2 * Real.sqrt (1 + Real.log (b / a)) := by
  rw [logScaleIntegral ha hab]
  have hsqrt : 0 ≤ Real.sqrt (1 + Real.log (b / a)) := Real.sqrt_nonneg _
  linarith

end

end Manhattan.Estimates
