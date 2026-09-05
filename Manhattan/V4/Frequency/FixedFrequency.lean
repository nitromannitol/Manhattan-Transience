import Manhattan.V4.Frequency.Profile
import Manhattan.V4.ScalarMinimization
import Manhattan.Estimates.Regional

/-!
# Version 4, Moves 2 and 3: the fixed-frequency bound

Move 1 of Version 4 supplies, for every real even `phi` supported on
`Γ_δ = {√δ ≤ |r| ≤ r₀}` with `δ = √λ + a(p)`,

  `r_λ(p) ≤ (1 - s ∫ phi dm)² / h₀ + C ∫_{Γ_δ} q phi² dm`,   `q(r) = |r|/√(log(1/|r|))`.

This file takes that inequality as a hypothesis and finishes the argument.

* `resolvent_le_of_effectiveEnergy` is Move 2: substituting the profile of
  `Manhattan/V4/Frequency/Profile.lean` turns both integrals into `Z_δ`
  (`profile_gammaIntegral`, `energy_gammaIntegral`), and the one-variable
  minimization of `Manhattan/V4/ScalarMinimization.lean` collapses the family
  over `t` to `1/(h₀ + s² Z_δ/C)`.
* `move3_bound` is Move 3: with `s² ≥ (2/π)² a²` and `Z_δ ≥ (1 + log(1/δ))^{3/2}/(30π)`
  the closed form becomes the Version 4 majorant

    `v4Majorant λ p = 1 / (λ + a(p)² (1 + log₊(1/(√λ + a(p))))^{3/2})`.

  Because that bound carries `λ` in its denominator, there is no separate case at
  `a ≤ √λ` and no `sin p₁ = 0` case; the minimization over `t` is unconstrained, so
  `s = 0` is not special.
-/

noncomputable section

namespace Manhattan.V4.Frequency

open MeasureTheory

/-! ### The exponent `3/2` -/

/-- `x^{3/2} = x √x`. -/
theorem rpow_three_halves {x : ℝ} (hx : 0 ≤ x) :
    x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
  rcases eq_or_lt_of_le hx with h | h
  · rw [← h, Real.zero_rpow (by norm_num), Real.sqrt_zero, mul_zero]
  · rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add h, Real.rpow_one,
      ← Real.sqrt_eq_rpow]

/-- `1 ≤ x` implies `1 ≤ x^{3/2}`. -/
theorem one_le_rpow_three_halves {x : ℝ} (hx : 1 ≤ x) : 1 ≤ x ^ (3 / 2 : ℝ) := by
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hsqrt : (1 : ℝ) ≤ Real.sqrt x := by
    have := Real.sqrt_le_sqrt hx
    simpa using this
  rw [rpow_three_halves hx0]
  nlinarith

/-- `x ↦ x^{3/2}` is monotone on the nonnegative reals. -/
theorem rpow_three_halves_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    x ^ (3 / 2 : ℝ) ≤ y ^ (3 / 2 : ℝ) :=
  Real.rpow_le_rpow hx hxy (by norm_num)

/-! ### Frequency vocabulary -/

/-- `θ(p) = d(p₁) + d(p₂) ≤ a(p)²`. -/
theorem theta_le_maxFrequency_sq (p : Fin 2 → ℝ) :
    Operator.theta p ≤ Operator.maxFrequency p ^ 2 := by
  rw [Manhattan.Estimates.operator_theta_eq]
  unfold Manhattan.Estimates.theta
  have h0 := Manhattan.Estimates.dispersion_le_half_mul_sq (p 0)
  have h1 := Manhattan.Estimates.dispersion_le_half_mul_sq (p 1)
  have key0 : (p 0) ^ 2 ≤ (max |p 0| |p 1|) ^ 2 := by
    have habs0 : |p 0| ≤ max |p 0| |p 1| := le_max_left _ _
    rw [← sq_abs]
    exact sq_le_sq' (by linarith [abs_nonneg (p 0), abs_nonneg (p 1)]) habs0
  have key1 : (p 1) ^ 2 ≤ (max |p 0| |p 1|) ^ 2 := by
    have habs1 : |p 1| ≤ max |p 0| |p 1| := le_max_right _ _
    rw [← sq_abs]
    exact sq_le_sq' (by linarith [abs_nonneg (p 0), abs_nonneg (p 1)]) habs1
  show Manhattan.Estimates.dispersion (p 0) + Manhattan.Estimates.dispersion (p 1)
      ≤ Operator.maxFrequency p ^ 2
  unfold Operator.maxFrequency
  nlinarith [h0, h1, key0, key1]

/-- `a(p) ≥ 0`. -/
theorem maxFrequency_nonneg (p : Fin 2 → ℝ) : 0 ≤ Operator.maxFrequency p :=
  le_trans (abs_nonneg (p 0)) (le_max_left _ _)

/-- `log₊` is monotone on the positive reals. -/
theorem logPos_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    Operator.logPos x ≤ Operator.logPos y := by
  show max (Real.log x) 0 ≤ max (Real.log y) 0
  exact max_le_max (Real.log_le_log hx hxy) le_rfl

/-- `log₊ ≥ 0`. -/
theorem logPos_nonneg (x : ℝ) : 0 ≤ Operator.logPos x := le_max_right _ _

/-- Jordan's inequality in squared form: `(2/π)² x² ≤ sin²x` for `|x| ≤ π/2`. -/
theorem sq_sin_ge {x : ℝ} (hx : |x| ≤ Real.pi / 2) :
    (2 / Real.pi) ^ 2 * x ^ 2 ≤ Real.sin x ^ 2 := by
  rw [abs_le] at hx
  obtain ⟨h_neg, h_pos⟩ := hx
  rcases le_or_gt 0 x with hx_nonneg | hx_neg
  · have h_sin : 2 / Real.pi * x ≤ Real.sin x := Real.mul_le_sin hx_nonneg h_pos
    have h_nonneg_a : 0 ≤ 2 / Real.pi * x :=
      mul_nonneg (div_nonneg (by norm_num) Real.pi_pos.le) hx_nonneg
    have h_sq : (2 / Real.pi * x) ^ 2 ≤ Real.sin x ^ 2 :=
      pow_le_pow_left₀ h_nonneg_a h_sin 2
    nlinarith [sq_nonneg x, sq_nonneg (Real.sin x)]
  · have hx_pos_neg : 0 ≤ -x := by linarith
    have hx_bound_neg : -x ≤ Real.pi / 2 := by linarith
    have h_sin : 2 / Real.pi * (-x) ≤ Real.sin (-x) :=
      Real.mul_le_sin hx_pos_neg hx_bound_neg
    rw [Real.sin_neg] at h_sin
    have h_nonneg_a : 0 ≤ 2 / Real.pi * (-x) :=
      mul_nonneg (div_nonneg (by norm_num) Real.pi_pos.le) hx_pos_neg
    have h_sq : (2 / Real.pi * (-x)) ^ 2 ≤ (-Real.sin x) ^ 2 :=
      pow_le_pow_left₀ h_nonneg_a h_sin 2
    nlinarith [sq_nonneg x, sq_nonneg (Real.sin x)]

/-- Under the standing assumption `δ ≤ r₀⁴`, `r₀ ≤ 1/4`, the logarithmic scale
`L = log(1/δ)` is at least `1`. -/
theorem one_le_negLog {r0 delta : ℝ} (hr0 : 0 < r0) (hr01 : r0 ≤ 1 / 4)
    (hd : 0 < delta) (hdle : delta ≤ r0 ^ 4) : 1 ≤ -Real.log delta := by
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have hhalf := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2⁻¹ by norm_num)
    rw [Real.log_inv] at hhalf
    linarith
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hr0log : Real.log r0 ≤ Real.log (1 / 4) := Real.log_le_log hr0 hr01
  have hquarter : Real.log (1 / 4 : ℝ) = -Real.log 4 := by
    rw [one_div, Real.log_inv]
  have hdlog : Real.log delta ≤ Real.log (r0 ^ 4) := Real.log_le_log hd hdle
  rw [Real.log_pow] at hdlog
  push_cast at hdlog
  rw [hquarter] at hr0log
  linarith

/-! ### The Version 4 fixed-frequency majorant -/

/-- The Version 4 logarithmic scale `1 + log₊(1/(√λ + a(p)))`. -/
def v4LogScale (lambda : ℝ) (p : Fin 2 → ℝ) : ℝ :=
  1 + Operator.logPos (1 / (Real.sqrt lambda + Operator.maxFrequency p))

/-- The Version 4 fixed-frequency majorant of Move 3,
`1 / (λ + a(p)² (1 + log₊(1/(√λ + a(p))))^{3/2})`. -/
def v4Majorant (lambda : ℝ) (p : Fin 2 → ℝ) : ℝ :=
  1 / (lambda + Operator.maxFrequency p ^ 2 * v4LogScale lambda p ^ (3 / 2 : ℝ))

theorem one_le_v4LogScale (lambda : ℝ) (p : Fin 2 → ℝ) : 1 ≤ v4LogScale lambda p := by
  have := logPos_nonneg (1 / (Real.sqrt lambda + Operator.maxFrequency p))
  unfold v4LogScale
  linarith

theorem one_le_v4LogScale_rpow (lambda : ℝ) (p : Fin 2 → ℝ) :
    1 ≤ v4LogScale lambda p ^ (3 / 2 : ℝ) :=
  one_le_rpow_three_halves (one_le_v4LogScale lambda p)

/-- The denominator of `v4Majorant` is strictly positive, so no junk value can
appear: the majorant is a genuine positive real. -/
theorem v4Majorant_denom_pos {lambda : ℝ} (hlambda : 0 < lambda) (p : Fin 2 → ℝ) :
    0 < lambda + Operator.maxFrequency p ^ 2 * v4LogScale lambda p ^ (3 / 2 : ℝ) := by
  have h := one_le_v4LogScale_rpow lambda p
  have ha : 0 ≤ Operator.maxFrequency p ^ 2 := sq_nonneg _
  nlinarith

theorem v4Majorant_pos {lambda : ℝ} (hlambda : 0 < lambda) (p : Fin 2 → ℝ) :
    0 < v4Majorant lambda p :=
  div_pos one_pos (v4Majorant_denom_pos hlambda p)

/-! ### Move 2 -/

/-- Move 2, scalar form: an effective-energy bound valid for every real `t`
collapses to the closed form of the one-variable minimization. -/
theorem move2_bound {rl h0 s C Z : ℝ} (hh0 : 0 < h0) (hZ : 0 < Z) (hC : 0 < C)
    (hMove1 : ∀ t : ℝ, rl ≤ (1 - s * (t * Z)) ^ 2 / h0 + C * (t ^ 2 * Z)) :
    rl ≤ 1 / (h0 + s ^ 2 * Z / C) := by
  have h := hMove1 (s / (C * h0 + s ^ 2 * Z))
  have hEq : (1 - s * (s / (C * h0 + s ^ 2 * Z) * Z)) ^ 2 / h0
        + C * ((s / (C * h0 + s ^ 2 * Z)) ^ 2 * Z)
      = (1 - s * (s / (C * h0 + s ^ 2 * Z)) * Z) ^ 2 / h0
        + C * (s / (C * h0 + s ^ 2 * Z)) ^ 2 * Z := by ring
  rw [hEq] at h
  have key := Manhattan.V4.oneVariable_eq hh0 hZ hC (s := s)
  linarith [key]

/-- `√δ ≤ r₀` under the standing hypotheses. -/
theorem sqrt_le_of_le_pow_four {r0 delta : ℝ} (hr0 : 0 < r0) (hr01 : r0 ≤ 1 / 4)
    (hle : delta ≤ r0 ^ 4) : Real.sqrt delta ≤ r0 := by
  have hr2 : r0 ^ 2 ≤ 1 := by nlinarith
  have h1 : delta ≤ r0 ^ 2 := by nlinarith [sq_nonneg r0]
  calc Real.sqrt delta ≤ Real.sqrt (r0 ^ 2) := Real.sqrt_le_sqrt h1
    _ = r0 := by rw [Real.sqrt_sq hr0.le]

/-- MOVE 2. The effective-energy inequality of Move 1, applied to the whole family
of profiles `phi(r) = t √(log(1/|r|))/|r|` on `Γ_δ`, yields the closed form
`1/(h₀ + s² Z_δ/C)`. The two substitution integrals are evaluated by
`profile_gammaIntegral` and `energy_gammaIntegral`, and the minimization over `t` is
`Manhattan.V4.oneVariable_eq`. -/
theorem resolvent_le_of_effectiveEnergy {r0 delta rl h0 s C : ℝ}
    (hr0 : 0 < r0) (hr01 : r0 ≤ 1 / 4) (hdelta : 0 < delta) (hdle : delta ≤ r0 ^ 4)
    (hh0 : 0 < h0) (hC : 0 < C)
    (hMove1 : ∀ t : ℝ,
      rl ≤ (1 - s * gammaIntegral r0 delta (profile r0 delta t)) ^ 2 / h0
          + C * gammaIntegral r0 delta
              (fun r => effectiveWeight r * profile r0 delta t r ^ 2)) :
    rl ≤ 1 / (h0 + s ^ 2 * Zdelta r0 delta / C) := by
  have hsq : 0 < Real.sqrt delta := Real.sqrt_pos.2 hdelta
  have hsqle : Real.sqrt delta ≤ r0 := sqrt_le_of_le_pow_four hr0 hr01 hdle
  have hr0lt : r0 < 1 := lt_of_le_of_lt hr01 (by norm_num)
  refine move2_bound hh0 (Zdelta_pos hr0 hr01 hdelta hdle) hC ?_
  intro t
  have h := hMove1 t
  rw [profile_gammaIntegral hsq hsqle t, energy_gammaIntegral hsq hsqle hr0lt t] at h
  exact h

/-! ### Move 3 -/

/-- The Version 4 logarithmic scale `(1 + log(1/δ))^{3/2}` is dominated by `Z_δ`,
with an explicit constant. -/
theorem rpow_le_Zdelta {r0 delta : ℝ} (hr0 : 0 < r0) (hr01 : r0 ≤ 1 / 4)
    (hd : 0 < delta) (hdle : delta ≤ r0 ^ 4) :
    (1 + -Real.log delta) ^ (3 / 2 : ℝ) ≤ 30 * Real.pi * Zdelta r0 delta := by
  have hL : 1 ≤ -Real.log delta := one_le_negLog hr0 hr01 hd hdle
  set L := -Real.log delta with hLdef
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hpi : 0 < Real.pi := Real.pi_pos
  have hLpos : 0 < L := by linarith
  have hX : 0 ≤ L * Real.sqrt L := by positivity
  have h1 : (1 + L) ^ (3 / 2 : ℝ) ≤ (2 * L) ^ (3 / 2 : ℝ) :=
    rpow_three_halves_mono (by linarith) (by linarith)
  have h2 : (2 * L) ^ (3 / 2 : ℝ) = 2 * L * Real.sqrt (2 * L) :=
    rpow_three_halves (by linarith)
  have h3 : 2 * L * Real.sqrt (2 * L) = 2 * Real.sqrt 2 * (L * Real.sqrt L) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) L]
    ring
  have h4 : L * Real.sqrt L / (6 * Real.sqrt 2 * Real.pi) ≤ Zdelta r0 delta :=
    (Zdelta_bounds hr0 hr01 hd hdle).1
  have h5 : 30 * Real.pi * (L * Real.sqrt L / (6 * Real.sqrt 2 * Real.pi))
      ≤ 30 * Real.pi * Zdelta r0 delta :=
    mul_le_mul_of_nonneg_left h4 (by positivity)
  have h6 : 2 * Real.sqrt 2 * (L * Real.sqrt L)
      ≤ 30 * Real.pi * (L * Real.sqrt L / (6 * Real.sqrt 2 * Real.pi)) := by
    have heq : 30 * Real.pi * (L * Real.sqrt L / (6 * Real.sqrt 2 * Real.pi))
        = 5 * (L * Real.sqrt L) / Real.sqrt 2 := by
      field_simp
      ring
    rw [heq, le_div_iff₀ hs2pos]
    nlinarith [hs2, hX]
  calc (1 + L) ^ (3 / 2 : ℝ) ≤ (2 * L) ^ (3 / 2 : ℝ) := h1
    _ = 2 * L * Real.sqrt (2 * L) := h2
    _ = 2 * Real.sqrt 2 * (L * Real.sqrt L) := h3
    _ ≤ 30 * Real.pi * (L * Real.sqrt L / (6 * Real.sqrt 2 * Real.pi)) := h6
    _ ≤ 30 * Real.pi * Zdelta r0 delta := h5

/-- On the improvement region the logarithmic scale is the plain logarithm. -/
theorem v4LogScale_eq {r0 lambda : ℝ} {p : Fin 2 → ℝ} (hr0 : 0 < r0) (hr01 : r0 ≤ 1 / 4)
    (hlambda : 0 < lambda)
    (hdle : Real.sqrt lambda + Operator.maxFrequency p ≤ r0 ^ 4) :
    v4LogScale lambda p = 1 + -Real.log (Real.sqrt lambda + Operator.maxFrequency p) := by
  have hdpos : 0 < Real.sqrt lambda + Operator.maxFrequency p :=
    add_pos_of_pos_of_nonneg (Real.sqrt_pos.2 hlambda) (maxFrequency_nonneg p)
  have hdlt1 : Real.sqrt lambda + Operator.maxFrequency p < 1 := by
    have h4 : r0 ^ 4 ≤ (1 / 4 : ℝ) ^ 4 := pow_le_pow_left₀ hr0.le hr01 4
    norm_num at h4
    linarith
  have hlogneg := Real.log_neg hdpos hdlt1
  unfold v4LogScale Operator.logPos
  rw [one_div, Real.log_inv, max_eq_left (by linarith : (0 : ℝ) ≤ -Real.log _)]

/-! The three scalar steps of Move 3, isolated so that the arithmetic runs on opaque
reals rather than on the frequency expressions they abbreviate. -/

private theorem move3_lower {A K P C : ℝ} (hA : 0 ≤ A) (hP : 0 < P) (hC : 0 < C)
    (hK2 : 15 * P * C ≤ 2 * K) : A ≤ K * (2 * A / (15 * P) / C) := by
  have hrw : K * (2 * A / (15 * P) / C) = 2 * K * A / (15 * P * C) := by
    field_simp
  rw [hrw, le_div_iff₀ (by positivity : (0 : ℝ) < 15 * P * C)]
  nlinarith

private theorem move3_assemble {lambda th sZC A K : ℝ}
    (hlambda : 0 < lambda) (hth : 0 ≤ th) (hK1 : 1 ≤ K) (hlow : A ≤ K * sZC) :
    lambda + A ≤ K * (lambda + th + sZC) := by
  have h2 : lambda ≤ K * lambda := le_mul_of_one_le_left hlambda.le hK1
  have h3 : 0 ≤ K * th := mul_nonneg (by linarith) hth
  have hexp : K * (lambda + th + sZC) = K * lambda + K * th + K * sZC := by ring
  rw [hexp]
  linarith

private theorem move3_div {rl D E K : ℝ} (hD : 0 < D) (hE : 0 < E)
    (hrl : rl ≤ 1 / D) (hkey : E ≤ K * D) : rl ≤ K * (1 / E) := by
  have hstep : 1 / D ≤ K * (1 / E) := by
    rw [mul_one_div, div_le_div_iff₀ hD hE]
    linarith
  linarith

/-- MOVE 3. With `s² ≥ (2/π)² a(p)²` and `h₀ = λ + θ(p)`, the closed form of Move 2
is the Version 4 fixed-frequency majorant (3). The bound carries `λ`, so it needs no
separate case at `a ≤ √λ` and no `sin p₁ = 0` case. -/
theorem move3_bound {r0 lambda rl s C : ℝ} {p : Fin 2 → ℝ}
    (hr0 : 0 < r0) (hr01 : r0 ≤ 1 / 4) (hlambda : 0 < lambda) (hC : 0 < C)
    (hs : (2 / Real.pi) ^ 2 * Operator.maxFrequency p ^ 2 ≤ s ^ 2)
    (hdle : Real.sqrt lambda + Operator.maxFrequency p ≤ r0 ^ 4)
    (hmove2 : rl ≤ 1 / (lambda + Operator.theta p
        + s ^ 2 * Zdelta r0 (Real.sqrt lambda + Operator.maxFrequency p) / C)) :
    rl ≤ max 1 (8 * Real.pi ^ 3 * C) * v4Majorant lambda p := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hanonneg : 0 ≤ Operator.maxFrequency p := maxFrequency_nonneg p
  have hdpos : 0 < Real.sqrt lambda + Operator.maxFrequency p :=
    add_pos_of_pos_of_nonneg (Real.sqrt_pos.2 hlambda) hanonneg
  have hLam1 : 1 ≤ v4LogScale lambda p ^ (3 / 2 : ℝ) := one_le_v4LogScale_rpow lambda p
  have hLamnn : 0 ≤ Operator.maxFrequency p ^ 2 * v4LogScale lambda p ^ (3 / 2 : ℝ) := by
    positivity
  have hthetann : 0 ≤ Operator.theta p := by
    rw [Manhattan.Estimates.operator_theta_eq]
    exact Manhattan.Estimates.theta_nonneg p
  have hZpos : 0 < Zdelta r0 (Real.sqrt lambda + Operator.maxFrequency p) :=
    Zdelta_pos hr0 hr01 hdpos hdle
  -- `Z_δ ≥ Λ^{3/2} / (30 π)`.
  have hrpow : v4LogScale lambda p ^ (3 / 2 : ℝ)
      ≤ 30 * Real.pi * Zdelta r0 (Real.sqrt lambda + Operator.maxFrequency p) := by
    rw [v4LogScale_eq hr0 hr01 hlambda hdle]
    exact rpow_le_Zdelta hr0 hr01 hdpos hdle
  have hZlow : v4LogScale lambda p ^ (3 / 2 : ℝ) / (30 * Real.pi)
      ≤ Zdelta r0 (Real.sqrt lambda + Operator.maxFrequency p) := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 30 * Real.pi)]
    linarith [hrpow]
  -- `s² Z_δ ≥ 2 a² Λ^{3/2} / (15 π³)`.
  have hprod : (2 / Real.pi) ^ 2 * Operator.maxFrequency p ^ 2
        * (v4LogScale lambda p ^ (3 / 2 : ℝ) / (30 * Real.pi))
      ≤ s ^ 2 * Zdelta r0 (Real.sqrt lambda + Operator.maxFrequency p) :=
    mul_le_mul hs hZlow (by positivity) (sq_nonneg s)
  have heq : (2 / Real.pi) ^ 2 * Operator.maxFrequency p ^ 2
        * (v4LogScale lambda p ^ (3 / 2 : ℝ) / (30 * Real.pi))
      = 2 * (Operator.maxFrequency p ^ 2 * v4LogScale lambda p ^ (3 / 2 : ℝ))
        / (15 * Real.pi ^ 3) := by
    field_simp
    ring
  rw [heq] at hprod
  have hstep : 2 * (Operator.maxFrequency p ^ 2 * v4LogScale lambda p ^ (3 / 2 : ℝ))
        / (15 * Real.pi ^ 3) / C
      ≤ s ^ 2 * Zdelta r0 (Real.sqrt lambda + Operator.maxFrequency p) / C := by
    gcongr
  -- The constant.
  have hK1 : (1 : ℝ) ≤ max 1 (8 * Real.pi ^ 3 * C) := le_max_left _ _
  have hKpos : (0 : ℝ) < max 1 (8 * Real.pi ^ 3 * C) := lt_of_lt_of_le one_pos hK1
  have hK2 : 15 * Real.pi ^ 3 * C ≤ 2 * max 1 (8 * Real.pi ^ 3 * C) := by
    rcases le_or_gt 1 (8 * Real.pi ^ 3 * C) with h | h
    · have hKge : 8 * Real.pi ^ 3 * C ≤ max 1 (8 * Real.pi ^ 3 * C) := le_max_right _ _
      nlinarith [hpi, hC]
    · nlinarith [hK1, hpi, hC]
  have hlower : Operator.maxFrequency p ^ 2 * v4LogScale lambda p ^ (3 / 2 : ℝ)
      ≤ max 1 (8 * Real.pi ^ 3 * C)
        * (2 * (Operator.maxFrequency p ^ 2 * v4LogScale lambda p ^ (3 / 2 : ℝ))
            / (15 * Real.pi ^ 3) / C) :=
    move3_lower hLamnn (by positivity : (0 : ℝ) < Real.pi ^ 3) hC hK2
  have hlow : Operator.maxFrequency p ^ 2 * v4LogScale lambda p ^ (3 / 2 : ℝ)
      ≤ max 1 (8 * Real.pi ^ 3 * C)
        * (s ^ 2 * Zdelta r0 (Real.sqrt lambda + Operator.maxFrequency p) / C) :=
    le_trans hlower (mul_le_mul_of_nonneg_left hstep hKpos.le)
  have hkey := move3_assemble (lambda := lambda) (th := Operator.theta p)
    (sZC := s ^ 2 * Zdelta r0 (Real.sqrt lambda + Operator.maxFrequency p) / C)
    (A := Operator.maxFrequency p ^ 2 * v4LogScale lambda p ^ (3 / 2 : ℝ))
    (K := max 1 (8 * Real.pi ^ 3 * C)) hlambda hthetann hK1 hlow
  have hDpos : 0 < lambda + Operator.theta p
      + s ^ 2 * Zdelta r0 (Real.sqrt lambda + Operator.maxFrequency p) / C := by
    have hnn : 0 ≤ s ^ 2 * Zdelta r0 (Real.sqrt lambda + Operator.maxFrequency p) / C := by
      positivity
    linarith
  have hEpos : 0 < lambda + Operator.maxFrequency p ^ 2 * v4LogScale lambda p ^ (3 / 2 : ℝ) :=
    v4Majorant_denom_pos hlambda p
  have := move3_div hDpos hEpos hmove2 hkey
  simpa only [v4Majorant] using this

end Manhattan.V4.Frequency
