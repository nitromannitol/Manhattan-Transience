import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Version 4, Move 2: the logarithmic scale integral `Z_δ`

The Version 4 competitor uses the profile `phi(r) = t √(log(1/|r|))/|r|` on the
annulus `Γ_δ = {√δ ≤ |r| ≤ r₀}`, for which both `∫ phi dm` and the effective
energy `∫ q phi² dm` (with weight `q(r) = |r|/√(log(1/|r|))`) equal `t` resp.
`t²` times the single number

  `Z_δ = ∫_{√δ ≤ |r| ≤ r₀} √(log(1/|r|))/|r| dm(r)`,   `dm = dr/(2π)`.

This file evaluates that integral by the substitution `u = log(1/r)`, whose
antiderivative is `-(2/3) u^{3/2}`, and derives explicit two-sided constants:

  `L √L / (6 √2 π) ≤ Z_δ ≤ L √L / (3 √2 π)`,   `L = log(1/δ)`,

valid whenever `0 < r₀ ≤ 1/4` and `0 < δ ≤ r₀⁴`. The upper bound needs only
`δ ≤ r₀²`; the lower bound is where `δ ≤ r₀⁴` (the manuscript's standing
assumption `δ < r₀⁴`) is used, through `log(1/r₀) ≤ L/4`.

Everything is stated with `Real.sqrt`, so `L^{3/2}` appears as `L * √L`.
-/

noncomputable section

namespace Manhattan.V4

open MeasureTheory Set

/-- The antiderivative for the substitution `u = log(1/r)`:
`d/dr [-(2/3) (log(1/r))^{3/2}] = √(log(1/r))/r` on `(0,1)`. -/
theorem logSqrt_hasDerivAt {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    HasDerivAt (fun y : ℝ => -(2 / 3) * ((-Real.log y) * Real.sqrt (-Real.log y)))
      (Real.sqrt (-Real.log x) / x) x := by
  have hu : 0 < -Real.log x := by
    have := Real.log_neg hx hx1
    linarith
  have hlog : HasDerivAt (fun y : ℝ => -Real.log y) (-1 / x) x := by
    simpa [neg_div] using (Real.hasDerivAt_log hx.ne').neg
  have hs := hlog.sqrt hu.ne'
  have hp := hlog.mul hs
  have hfinal := hp.const_mul (-(2 / 3) : ℝ)
  convert hfinal using 1
  have hspos : 0 < Real.sqrt (-Real.log x) := Real.sqrt_pos.2 hu
  have hsq : Real.sqrt (-Real.log x) * Real.sqrt (-Real.log x) = -Real.log x :=
    Real.mul_self_sqrt hu.le
  field_simp
  nlinarith [hsq, hspos, hx]

/-- The integrand is continuous away from the origin, hence interval integrable. -/
theorem logSqrt_intervalIntegrable {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun r : ℝ => Real.sqrt (-Real.log r) / r) volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro x hx
  have hxIcc : x ∈ Set.Icc a b := by simpa [Set.uIcc_of_le hab] using hx
  have hxpos : 0 < x := ha.trans_le hxIcc.1
  apply ContinuousAt.continuousWithinAt
  exact ((Real.continuousAt_log hxpos.ne').neg.sqrt).div continuousAt_id hxpos.ne'

/-- The substitution `u = log(1/r)`: the exact value of the `√log` integral. -/
theorem logSqrtIntegral {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    (∫ r in a..b, Real.sqrt (-Real.log r) / r)
      = (2 / 3) * ((-Real.log a) * Real.sqrt (-Real.log a))
        - (2 / 3) * ((-Real.log b) * Real.sqrt (-Real.log b)) := by
  have hderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun y : ℝ => -(2 / 3) * ((-Real.log y) * Real.sqrt (-Real.log y)))
        (Real.sqrt (-Real.log x) / x) x := by
    intro x hx
    have hxIcc : x ∈ Set.Icc a b := by simpa [Set.uIcc_of_le hab] using hx
    exact logSqrt_hasDerivAt (ha.trans_le hxIcc.1) (lt_of_le_of_lt hxIcc.2 hb)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (logSqrt_intervalIntegrable ha hab)]
  ring

/-- Two-sided bound for the normalized `Z_δ` integral, with explicit constants. -/
theorem logSqrtNormalized_bounds {r0 delta : ℝ} (hr0 : 0 < r0) (hr01 : r0 ≤ 1 / 4)
    (hdelta : 0 < delta) (hle : delta ≤ r0 ^ 4) :
    (-Real.log delta) * Real.sqrt (-Real.log delta) / (6 * Real.sqrt 2 * Real.pi)
        ≤ (1 / Real.pi) * ∫ r in Real.sqrt delta..r0, Real.sqrt (-Real.log r) / r
      ∧ (1 / Real.pi) * ∫ r in Real.sqrt delta..r0, Real.sqrt (-Real.log r) / r
        ≤ (-Real.log delta) * Real.sqrt (-Real.log delta) / (3 * Real.sqrt 2 * Real.pi) := by
  have hr0lt1 : r0 < 1 := lt_of_le_of_lt hr01 (by norm_num)
  have hdlt1 : delta < 1 := by
    have h4 : r0 ^ 4 ≤ (1 / 4 : ℝ) ^ 4 := pow_le_pow_left₀ hr0.le hr01 4
    norm_num at h4
    linarith
  have hsq : 0 < Real.sqrt delta := Real.sqrt_pos.2 hdelta
  have hsqle : Real.sqrt delta ≤ r0 := by
    have h1 : delta ≤ r0 ^ 2 := by nlinarith
    calc Real.sqrt delta ≤ Real.sqrt (r0 ^ 2) := Real.sqrt_le_sqrt h1
      _ = r0 := by rw [Real.sqrt_sq hr0.le]
  have hI := logSqrtIntegral hsq hsqle hr0lt1
  set Ld : ℝ := -Real.log delta with hLd
  set w : ℝ := -Real.log r0 with hw
  have hLdpos : 0 < Ld := by
    have := Real.log_neg hdelta hdlt1
    simp only [hLd]; linarith
  have hwpos : 0 < w := by
    have := Real.log_neg hr0 hr0lt1
    simp only [hw]; linarith
  have hlogsq : -Real.log (Real.sqrt delta) = Ld / 2 := by
    rw [Real.log_sqrt hdelta.le]; simp only [hLd]; ring
  have hw4 : w ≤ Ld / 4 := by
    have h1 : Real.log delta ≤ Real.log (r0 ^ 4) := Real.log_le_log hdelta hle
    rw [Real.log_pow] at h1
    simp only [hLd, hw]
    push_cast at h1
    linarith
  rw [hlogsq] at hI
  set S : ℝ := Real.sqrt Ld with hS
  set s2 : ℝ := Real.sqrt 2 with hs2
  have hSpos : 0 < S := Real.sqrt_pos.2 hLdpos
  have hs2pos : 0 < s2 := Real.sqrt_pos.2 (by norm_num)
  have hs2sq : s2 * s2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs2le : s2 ≤ 2 := by nlinarith
  have hhalf : Real.sqrt (Ld / 2) = S / s2 := Real.sqrt_div hLdpos.le 2
  have hquarter : Real.sqrt (Ld / 4) = S / 2 := by
    rw [Real.sqrt_div hLdpos.le 4, show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
  have hwbound : w * Real.sqrt w ≤ Ld * S / 8 := by
    have h1 : Real.sqrt w ≤ S / 2 := by
      rw [← hquarter]; exact Real.sqrt_le_sqrt hw4
    have h2 : 0 ≤ Real.sqrt w := Real.sqrt_nonneg _
    nlinarith [hwpos.le, hSpos.le]
  have hwnn : 0 ≤ w * Real.sqrt w := mul_nonneg hwpos.le (Real.sqrt_nonneg _)
  rw [hhalf] at hI
  have hPnn : 0 ≤ Ld * S := by positivity
  have heq : 2 / 3 * (Ld / 2 * (S / s2)) = Ld * S / (3 * s2) := by
    field_simp
  rw [heq] at hI
  have hpi : 0 < Real.pi := Real.pi_pos
  have hdouble : Ld * S / (3 * s2) = 2 * (Ld * S / (6 * s2)) := by
    field_simp; ring
  have hgap : Ld * S / 12 ≤ Ld * S / (6 * s2) := by
    rw [div_le_div_iff_of_pos_left (by positivity) (by norm_num) (by positivity)]
    linarith
  have hIupper : (∫ r in Real.sqrt delta..r0, Real.sqrt (-Real.log r) / r)
      ≤ Ld * S / (3 * s2) := by
    rw [hI]; linarith
  have hIlower : Ld * S / (6 * s2)
      ≤ ∫ r in Real.sqrt delta..r0, Real.sqrt (-Real.log r) / r := by
    rw [hI]; linarith
  have hsplit6 : Ld * S / (6 * s2 * Real.pi) = 1 / Real.pi * (Ld * S / (6 * s2)) := by
    field_simp
  have hsplit3 : Ld * S / (3 * s2 * Real.pi) = 1 / Real.pi * (Ld * S / (3 * s2)) := by
    field_simp
  refine ⟨?_, ?_⟩
  · rw [hsplit6]
    exact mul_le_mul_of_nonneg_left hIlower (by positivity)
  · rw [hsplit3]
    exact mul_le_mul_of_nonneg_left hIupper (by positivity)

/-- `Z_δ = ∫_{√δ ≤ |r| ≤ r₀} √(log(1/|r|))/|r| dm(r)` with `dm = dr/(2π)`, written as the
two interval integrals over the two components of the annulus. -/
def Zdelta (r0 delta : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ *
    ((∫ r in -r0..(-Real.sqrt delta), Real.sqrt (-Real.log |r|) / |r|)
      + ∫ r in Real.sqrt delta..r0, Real.sqrt (-Real.log |r|) / |r|)

/-- The integrand is even, so `Z_δ` is `(1/π)` times the one-sided integral. -/
theorem Zdelta_eq {r0 delta : ℝ} (hsq : 0 < Real.sqrt delta) (hsqle : Real.sqrt delta ≤ r0) :
    Zdelta r0 delta = (1 / Real.pi) * ∫ r in Real.sqrt delta..r0, Real.sqrt (-Real.log r) / r := by
  have hpos : (∫ r in Real.sqrt delta..r0, Real.sqrt (-Real.log |r|) / |r|)
      = ∫ r in Real.sqrt delta..r0, Real.sqrt (-Real.log r) / r := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    have hxIcc : x ∈ Set.Icc (Real.sqrt delta) r0 := by
      simpa [Set.uIcc_of_le hsqle] using hx
    rw [abs_of_pos (hsq.trans_le hxIcc.1)]
  have hneg : (∫ r in -r0..(-Real.sqrt delta), Real.sqrt (-Real.log |r|) / |r|)
      = ∫ r in Real.sqrt delta..r0, Real.sqrt (-Real.log |r|) / |r| := by
    rw [← intervalIntegral.integral_comp_neg (a := Real.sqrt delta) (b := r0)
      (fun r : ℝ => Real.sqrt (-Real.log |r|) / |r|)]
    simp
  rw [Zdelta, hneg, hpos]
  field_simp
  ring

/-- `Z_δ ≍ [log(1/δ)]^{3/2}` with explicit two-sided constants. -/
theorem Zdelta_bounds {r0 delta : ℝ} (hr0 : 0 < r0) (hr01 : r0 ≤ 1 / 4)
    (hdelta : 0 < delta) (hle : delta ≤ r0 ^ 4) :
    (-Real.log delta) * Real.sqrt (-Real.log delta) / (6 * Real.sqrt 2 * Real.pi)
        ≤ Zdelta r0 delta
      ∧ Zdelta r0 delta
        ≤ (-Real.log delta) * Real.sqrt (-Real.log delta) / (3 * Real.sqrt 2 * Real.pi) := by
  have hr0lt1 : r0 < 1 := lt_of_le_of_lt hr01 (by norm_num)
  have hsq : 0 < Real.sqrt delta := Real.sqrt_pos.2 hdelta
  have hsqle : Real.sqrt delta ≤ r0 := by
    have hr2 : r0 ^ 2 ≤ 1 := by nlinarith
    have h1 : delta ≤ r0 ^ 2 := by nlinarith [sq_nonneg r0]
    calc Real.sqrt delta ≤ Real.sqrt (r0 ^ 2) := Real.sqrt_le_sqrt h1
      _ = r0 := by rw [Real.sqrt_sq hr0.le]
  rw [Zdelta_eq hsq hsqle]
  exact logSqrtNormalized_bounds hr0 hr01 hdelta hle

end Manhattan.V4
