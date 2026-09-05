import Mathlib.Analysis.Complex.ExponentialBounds
import Manhattan.Estimates.KernelBound

/-!
# Version 4, Move 1: the logarithmic scale and the effective weight

This file collects the elementary one-variable estimates behind ingredient (e)
of Move 1 of the Version 4 argument:

    `sin² r ≤ r²` and `δ + r² ≤ 2 r² ≤ q(r)` on `Γ_δ = {√δ ≤ |r| ≤ r₀}`,

where the **effective weight** is `q(r) = |r| / √(log(1/|r|))` and `r₀ = 1/4`.
The last inequality is the statement that `|r| √(log(1/|r|))` is bounded on
`(0, 1/4]`; the explicit bound proved here is `≤ 1/2`, which makes the constant
in `δ + r² ≤ q(r)` equal to one.

Everything rests on one elementary comparison, `log(1/r) ≤ 2/√r`, obtained from
`log x ≤ x - 1` at `x = 1/√r`. It also gives `r log(1/r) ≤ 1`, which is what
lets the outer part of the `β` integral of `Manhattan/V4/Energy/BetaIntegral.lean`
be absorbed into the main term.
-/

namespace Manhattan.V4.Energy

/-! ## The logarithmic scale on `(0, 1/4]` -/

/-- `log(1/r) ≤ 2/√r`. This is `log x ≤ x - 1` at `x = 1/√r`. -/
theorem log_inv_le_two_div_sqrt {r : ℝ} (hr : 0 < r) :
    Real.log (1 / r) ≤ 2 / Real.sqrt r := by
  set u := Real.sqrt r
  have hu_pos : 0 < u := Real.sqrt_pos.mpr hr
  have h_log_sqrt : Real.log u = Real.log r / 2 := Real.log_sqrt hr.le
  have hu_inv_pos : 0 < u⁻¹ := by positivity
  have h_log_inv_ineq : Real.log u⁻¹ ≤ u⁻¹ - 1 := Real.log_le_sub_one_of_pos hu_inv_pos
  have h_log_inv_u : Real.log u⁻¹ = -Real.log u := Real.log_inv u
  rw [h_log_inv_u, h_log_sqrt] at h_log_inv_ineq
  have key_step : -Real.log r ≤ 2 * u⁻¹ := by nlinarith
  have key : -Real.log r ≤ 2 / u := by rw [div_eq_mul_inv]; exact key_step
  have h_log_one_div : Real.log (1 / r) = -Real.log r := by
    rw [Real.log_div (by norm_num : (1:ℝ) ≠ 0) hr.ne']
    simp
  linarith

/-- `√r ≤ 1/2` for `0 ≤ r ≤ 1/4`. -/
theorem sqrt_le_half {r : ℝ} (hr1 : r ≤ 1 / 4) : Real.sqrt r ≤ 1 / 2 := by
  have h4 : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [← h4]
  exact Real.sqrt_le_sqrt hr1

/-- `r² log(1/r) ≤ 1/4` on `(0, 1/4]`. -/
theorem sq_mul_log_inv_le {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1 / 4) :
    r ^ 2 * Real.log (1 / r) ≤ 1 / 4 := by
  have sqrt_r_le : Real.sqrt r ≤ 1 / 2 := sqrt_le_half hr1
  have log_ineq : Real.log (1 / r) ≤ 2 / Real.sqrt r := log_inv_le_two_div_sqrt hr
  have mul_ineq : r ^ 2 * Real.log (1 / r) ≤ r ^ 2 * (2 / Real.sqrt r) := by
    apply mul_le_mul_of_nonneg_left log_ineq
    positivity
  have h_sqrt_sq : Real.sqrt r * Real.sqrt r = r := Real.mul_self_sqrt hr.le
  have simplify : r ^ 2 * (2 / Real.sqrt r) = 2 * r * Real.sqrt r := by
    field_simp
    nlinarith [Real.sqrt_nonneg r]
  rw [simplify] at mul_ineq
  nlinarith [sqrt_r_le, Real.sqrt_nonneg r]

/-- `r log(1/r) ≤ 1` on `(0, 1/4]`. -/
theorem mul_log_inv_le_one {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1 / 4) :
    r * Real.log (1 / r) ≤ 1 := by
  have sqrt_r_le : Real.sqrt r ≤ 1 / 2 := sqrt_le_half hr1
  have log_ineq : Real.log (1 / r) ≤ 2 / Real.sqrt r := log_inv_le_two_div_sqrt hr
  have mul_ineq : r * Real.log (1 / r) ≤ r * (2 / Real.sqrt r) := by
    apply mul_le_mul_of_nonneg_left log_ineq
    linarith
  have simplify : r * (2 / Real.sqrt r) = 2 * Real.sqrt r := by
    field_simp
    nlinarith [Real.sqrt_nonneg r, Real.mul_self_sqrt hr.le]
  rw [simplify] at mul_ineq
  nlinarith [sqrt_r_le]

/-- `0 < log(1/r)` on `(0, 1/4]`. -/
theorem log_inv_pos {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1 / 4) :
    0 < Real.log (1 / r) := by
  have h_one_div : 1 < 1 / r := by rw [one_lt_div hr]; linarith
  exact Real.log_pos h_one_div

/-- `1 < log(1/r)` on `(0, 1/4]`, because `1/r ≥ 4 > e`. This is the reason
`√(log(1/ρ)) > 1`, used to place the inner threshold `ρ/√(log(1/ρ))` below `√ρ`. -/
theorem one_lt_log_inv {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1 / 4) :
    1 < Real.log (1 / r) := by
  have h_inv_pos : 0 < 1 / r := by positivity
  rw [Real.lt_log_iff_exp_lt h_inv_pos]
  have h_four : (4 : ℝ) ≤ 1 / r := by rw [le_div_iff₀ hr]; linarith
  have h_exp : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  norm_num at *
  linarith

/-- `r ≤ √r` for `0 ≤ r ≤ 1`. -/
theorem le_sqrt_self {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) : r ≤ Real.sqrt r := by
  rw [Real.le_sqrt hr hr]
  nlinarith [sq_nonneg r]

/-- `r √(log(1/r)) ≤ 1/2` on `(0, 1/4]`: the boundedness that makes `δ + r²`
dominated by the effective weight. -/
theorem mul_sqrt_log_inv_le_half {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1 / 4) :
    r * Real.sqrt (Real.log (1 / r)) ≤ 1 / 2 := by
  set L := Real.log (1 / r)
  have hL_pos : 0 < L := log_inv_pos hr hr1
  have h_sq_sqrt : Real.sqrt L ^ 2 = L := Real.sq_sqrt hL_pos.le
  have key : (r * Real.sqrt L) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    rw [mul_pow, h_sq_sqrt]
    have := sq_mul_log_inv_le hr hr1
    norm_num
    linarith
  nlinarith [key, sq_nonneg (r * Real.sqrt L - 1 / 2), Real.sqrt_nonneg L, hr]

/-! ## The effective weight -/

/-- The **effective weight** `q(r) = |r| / √(log(1/|r|))` of Move 1 (1) of
Version 4. Off `(0,1)` this is a junk value (`q(0) = 0`); every statement below
constrains `r` to `Γ_δ ⊆ (0, 1/4]` in absolute value. -/
noncomputable def effectiveWeight (r : ℝ) : ℝ :=
  |r| / Real.sqrt (Real.log (1 / |r|))

theorem effectiveWeight_pos {r : ℝ} (hr : 0 < |r|) (hr1 : |r| ≤ 1 / 4) :
    0 < effectiveWeight r := by
  unfold effectiveWeight
  exact div_pos hr (Real.sqrt_pos.mpr (log_inv_pos hr hr1))

theorem effectiveWeight_nonneg (r : ℝ) : 0 ≤ effectiveWeight r := by
  unfold effectiveWeight
  positivity

theorem measurable_effectiveWeight : Measurable effectiveWeight := by
  unfold effectiveWeight
  have habs : Measurable (fun r : ℝ => |r|) := continuous_abs.measurable
  exact habs.div
    (Real.continuous_sqrt.measurable.comp
      (Real.measurable_log.comp (measurable_const.div habs)))

/-- `q(r) ≤ |r|` on `0 < |r| ≤ 1/4`, because `log(1/|r|) ≥ log 4 > 1`. -/
theorem effectiveWeight_le_abs {r : ℝ} (hr : 0 < |r|) (hr1 : |r| ≤ 1 / 4) :
    effectiveWeight r ≤ |r| := by
  unfold effectiveWeight
  have hL : 1 < Real.log (1 / |r|) := one_lt_log_inv hr hr1
  have hS : 1 ≤ Real.sqrt (Real.log (1 / |r|)) := by
    have h1 : Real.sqrt 1 ≤ Real.sqrt (Real.log (1 / |r|)) := Real.sqrt_le_sqrt hL.le
    simpa using h1
  exact div_le_self hr.le hS

/-- `2 r² ≤ q(r)` on `0 < |r| ≤ 1/4`. -/
theorem two_mul_sq_le_effectiveWeight {r : ℝ} (hr : 0 < |r|) (hr1 : |r| ≤ 1 / 4) :
    2 * r ^ 2 ≤ effectiveWeight r := by
  unfold effectiveWeight
  rw [← sq_abs r]
  have hSqrt : 0 < Real.sqrt (Real.log (1 / |r|)) := Real.sqrt_pos.mpr (log_inv_pos hr hr1)
  rw [le_div_iff₀ hSqrt]
  nlinarith [mul_sqrt_log_inv_le_half hr hr1, abs_nonneg r,
    Real.sqrt_nonneg (Real.log (1 / |r|)), hr]

/-- **Ingredient (e) of Move 1.** On `Γ_δ = {√δ ≤ |r| ≤ 1/4}` the degree-one
profile `δ + r²` is dominated by the effective weight, with constant one. -/
theorem add_sq_le_effectiveWeight {delta r : ℝ} (hd : 0 ≤ delta)
    (hdr : Real.sqrt delta ≤ |r|) (hr : 0 < |r|) (hr1 : |r| ≤ 1 / 4) :
    delta + r ^ 2 ≤ effectiveWeight r := by
  have h1 : delta ≤ r ^ 2 := by
    rw [← sq_abs r]
    nlinarith [Real.sq_sqrt hd, Real.sqrt_nonneg delta]
  have h2 : 2 * r ^ 2 ≤ effectiveWeight r := two_mul_sq_le_effectiveWeight hr hr1
  linarith

/-! ## The trigonometric comparisons -/

/-- Jordan's inequality, squared: `(2/π)² β² ≤ sin² β` for `|β| ≤ π/2`. -/
theorem sq_le_sin_sq {b : ℝ} (hb : |b| ≤ Real.pi / 2) :
    4 / Real.pi ^ 2 * b ^ 2 ≤ Real.sin b ^ 2 := by
  have h1 := Real.mul_abs_le_abs_sin hb
  have h2 : (2 / Real.pi * |b|) ^ 2 ≤ |Real.sin b| ^ 2 :=
    pow_le_pow_left₀ (by positivity) h1 2
  rw [sq_abs] at h2
  have h4 : (2 / Real.pi * |b|) ^ 2 = 4 / Real.pi ^ 2 * b ^ 2 := by
    rw [mul_pow, sq_abs]; ring
  rw [h4] at h2
  exact h2

/-- `sin² β ≤ β²`. -/
theorem sin_sq_le_sq (b : ℝ) : Real.sin b ^ 2 ≤ b ^ 2 := Real.sin_sq_le_sq

/-- `2 β²/π² ≤ d(β) = 1 - cos β` for `|β| ≤ π`. -/
theorem two_sq_div_pi_sq_le_dispersion {b : ℝ} (hb : |b| ≤ Real.pi) :
    2 * b ^ 2 / Real.pi ^ 2 ≤ Manhattan.Estimates.dispersion b :=
  (Manhattan.Estimates.dispersion_quadratic_bounds hb).1

/-- The step that turns the `β`-integral bound `(6)`,
`∫ dm(β)/(B+σ) ≤ C/(|r| √(log(1/|r|)))`, into the effective weight:
`sin²(r) · C/(|r| √(log(1/|r|))) ≤ C q(r)`, using `sin² r ≤ r²`. -/
theorem sin_sq_mul_betaBound_le {r C : ℝ} (hC : 0 ≤ C) (hr : 0 < |r|)
    (hr1 : |r| ≤ 1 / 4) :
    Real.sin r ^ 2 * (C / (|r| * Real.sqrt (Real.log (1 / |r|))))
      ≤ C * effectiveWeight r := by
  set S := Real.sqrt (Real.log (1 / |r|)) with hS_def
  have hS_pos : 0 < S := Real.sqrt_pos.mpr (log_inv_pos hr hr1)
  have h_sin_sq : Real.sin r ^ 2 ≤ |r| ^ 2 := by rw [sq_abs]; exact Real.sin_sq_le_sq
  have h_factor_nonneg : 0 ≤ C / (|r| * S) := div_nonneg hC (by positivity)
  have h_mul : Real.sin r ^ 2 * (C / (|r| * S)) ≤ |r| ^ 2 * (C / (|r| * S)) :=
    mul_le_mul_of_nonneg_right h_sin_sq h_factor_nonneg
  have h_simplify : |r| ^ 2 * (C / (|r| * S)) = C * (|r| / S) := by
    field_simp [hr.ne', hS_pos.ne']
  rw [h_simplify] at h_mul
  unfold effectiveWeight
  rw [hS_def]
  exact h_mul

end Manhattan.V4.Energy
