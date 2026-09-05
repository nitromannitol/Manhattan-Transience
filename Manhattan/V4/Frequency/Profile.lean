import Manhattan.V4.LogScale

/-!
# Version 4, Move 2: the substitution `phi(r) = t √(log(1/|r|))/|r|`

Move 1 of Version 4 (the Version 4 argument) supplies, for every real even
`phi` supported on the annulus `Γ_δ = {√δ ≤ |r| ≤ r₀}`, the effective-energy bound

  `r_λ(p) ≤ (1 - s ∫ phi dm)² / h₀ + C ∫_{Γ_δ} q phi² dm`, `q(r) = |r|/√(log(1/|r|))`.

Move 2 substitutes the profile `phi(r) = t √(log(1/|r|))/|r|`. This file performs the
two computations that make the one-variable minimization applicable:

  `∫ phi dm = t Z_δ` and `∫ q phi² dm = t² Z_δ`,

with the single number `Z_δ = ∫_{Γ_δ} √(log(1/|r|))/|r| dm(r)` of
`Manhattan/V4/LogScale.lean`. Both are consequences of the pointwise identity

  `q(r) · (t √(log(1/|r|))/|r|)² = t² · √(log(1/|r|))/|r|`,

valid at every `r` with `0 < |r| < 1`, so the SAME integral carries both sides of the
minimization. That is the whole content of the substitution.

The file also records the two facts a consumer needs about the profile: it is even,
and it is bounded on the torus (`profile_abs_le`), which is the concrete discharge of
the `phi ∈ L²` gap left open -- for fixed `δ > 0` the profile is a bounded
function supported in a set of finite measure. The bound degrades as `δ → 0`, which is
harmless because `λ > 0` is fixed throughout.
-/

noncomputable section

namespace Manhattan.V4.Frequency

open MeasureTheory Set

/-- The scale weight `√(log(1/|r|))/|r|`, the integrand of `Z_δ`. -/
def logWeight (r : ℝ) : ℝ := Real.sqrt (-Real.log |r|) / |r|

/-- The effective weight `q(r) = |r|/√(log(1/|r|))` of Move 1. -/
def effectiveWeight (r : ℝ) : ℝ := |r| / Real.sqrt (-Real.log |r|)

/-- The annulus `Γ_δ = {√δ ≤ |r| ≤ r₀}` on which the competitor is supported. -/
def Gamma (r0 delta : ℝ) : Set ℝ := {r : ℝ | Real.sqrt delta ≤ |r| ∧ |r| ≤ r0}

/-- The Version 4 competitor profile `phi(r) = t √(log(1/|r|))/|r|` on `Γ_δ`,
extended by zero. -/
def profile (r0 delta t : ℝ) (r : ℝ) : ℝ :=
  if Real.sqrt delta ≤ |r| ∧ |r| ≤ r0 then t * logWeight r else 0

/-- The normalized Haar integral over `Γ_δ`, written as the sum of the two interval
integrals over its two components. This is the same shape as
`Manhattan.V4.Zdelta`. -/
def gammaIntegral (r0 delta : ℝ) (f : ℝ → ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ *
    ((∫ r in -r0..(-Real.sqrt delta), f r) + ∫ r in Real.sqrt delta..r0, f r)

/-- `Z_δ` is the `Γ_δ`-integral of the scale weight. -/
theorem Zdelta_eq_gammaIntegral (r0 delta : ℝ) :
    Zdelta r0 delta = gammaIntegral r0 delta logWeight := rfl

/-! ### Elementary properties of `gammaIntegral` -/

theorem gammaIntegral_const_mul (r0 delta c : ℝ) (f : ℝ → ℝ) :
    gammaIntegral r0 delta (fun r => c * f r) = c * gammaIntegral r0 delta f := by
  simp only [gammaIntegral, intervalIntegral.integral_const_mul]
  ring

theorem gammaIntegral_congr {r0 delta : ℝ} (hsq : 0 < Real.sqrt delta)
    (hle : Real.sqrt delta ≤ r0) {f g : ℝ → ℝ}
    (h : ∀ r : ℝ, Real.sqrt delta ≤ |r| → |r| ≤ r0 → f r = g r) :
    gammaIntegral r0 delta f = gammaIntegral r0 delta g := by
  unfold gammaIntegral
  have h_neg : -r0 ≤ -Real.sqrt delta := by linarith
  have int1 : (∫ r in -r0..(-Real.sqrt delta), f r)
      = ∫ r in -r0..(-Real.sqrt delta), g r := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le h_neg] at hx
    have hxneg : x < 0 := by linarith [hx.2]
    apply h x
    · show Real.sqrt delta ≤ |x|
      rw [abs_of_neg hxneg]
      linarith [hx.2]
    · show |x| ≤ r0
      rw [abs_of_neg hxneg]
      linarith [hx.1]
  have int2 : (∫ r in Real.sqrt delta..r0, f r) = ∫ r in Real.sqrt delta..r0, g r := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hle] at hx
    have hxpos : 0 < x := by linarith [hx.1, hsq]
    apply h x
    · show Real.sqrt delta ≤ |x|
      rw [abs_of_pos hxpos]
      exact hx.1
    · show |x| ≤ r0
      rw [abs_of_pos hxpos]
      exact hx.2
  simp [int1, int2]

/-! ### The pointwise substitution identity -/

/-- `x ↦ √(log(1/x))/x` is antitone on `(0,1)`. -/
theorem logWeight_antitone {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy : y < 1) :
    Real.sqrt (-Real.log y) / y ≤ Real.sqrt (-Real.log x) / x := by
  have hx1 : x < 1 := by linarith
  have hy_pos : 0 < y := by linarith
  have hlogxy : Real.log x ≤ Real.log y := Real.log_le_log hx hxy
  have hsqrts : Real.sqrt (-Real.log y) ≤ Real.sqrt (-Real.log x) :=
    Real.sqrt_le_sqrt (by linarith : -Real.log y ≤ -Real.log x)
  have sqrt_nonneg : 0 ≤ Real.sqrt (-Real.log y) := Real.sqrt_nonneg _
  gcongr

/-- The pointwise identity `q(r) · (t √(log(1/|r|))/|r|)² = t² √(log(1/|r|))/|r|`. -/
theorem effectiveWeight_mul_sq {r t : ℝ} (hr : 0 < |r|) (hr1 : |r| < 1) :
    (|r| / Real.sqrt (-Real.log |r|)) * (t * (Real.sqrt (-Real.log |r|) / |r|)) ^ 2
      = t ^ 2 * (Real.sqrt (-Real.log |r|) / |r|) := by
  set R := |r|
  set L := -Real.log |r|
  set S := Real.sqrt L
  have hR : 0 < R := hr
  have hLogNeg : Real.log |r| < 0 := Real.log_neg hr hr1
  have hL : 0 < L := by linarith
  have hS : 0 < S := Real.sqrt_pos.2 hL
  have hSS : S * S = L := Real.mul_self_sqrt hL.le
  field_simp

/-! ### The two substitution integrals -/

/-- The first substitution: `∫_{Γ_δ} phi dm = t Z_δ`. -/
theorem profile_gammaIntegral {r0 delta : ℝ} (hsq : 0 < Real.sqrt delta)
    (hle : Real.sqrt delta ≤ r0) (t : ℝ) :
    gammaIntegral r0 delta (profile r0 delta t) = t * Zdelta r0 delta := by
  rw [Zdelta_eq_gammaIntegral, ← gammaIntegral_const_mul]
  refine gammaIntegral_congr hsq hle ?_
  intro r hr1 hr2
  simp only [profile, if_pos (And.intro hr1 hr2)]

/-- The second substitution: `∫_{Γ_δ} q phi² dm = t² Z_δ`, with the effective weight
`q(r) = |r|/√(log(1/|r|))` of Move 1. -/
theorem energy_gammaIntegral {r0 delta : ℝ} (hsq : 0 < Real.sqrt delta)
    (hle : Real.sqrt delta ≤ r0) (hr01 : r0 < 1) (t : ℝ) :
    gammaIntegral r0 delta (fun r => effectiveWeight r * profile r0 delta t r ^ 2)
      = t ^ 2 * Zdelta r0 delta := by
  rw [Zdelta_eq_gammaIntegral, ← gammaIntegral_const_mul]
  refine gammaIntegral_congr hsq hle ?_
  intro r hr1 hr2
  have hrpos : 0 < |r| := lt_of_lt_of_le hsq hr1
  have hrlt : |r| < 1 := lt_of_le_of_lt hr2 hr01
  simp only [profile, if_pos (And.intro hr1 hr2), effectiveWeight, logWeight]
  exact effectiveWeight_mul_sq hrpos hrlt

/-! ### Non-degeneracy and the `L²` discharge -/

/-- `Z_δ` is strictly positive under the standing hypotheses, so the substitution
is not vacuous and the minimization of Move 2 is non-degenerate. -/
theorem Zdelta_pos {r0 delta : ℝ} (hr0 : 0 < r0) (hr01 : r0 ≤ 1 / 4)
    (hdelta : 0 < delta) (hle : delta ≤ r0 ^ 4) : 0 < Zdelta r0 delta := by
  have hdlt1 : delta < 1 := by
    have h4 : r0 ^ 4 ≤ (1 / 4 : ℝ) ^ 4 := pow_le_pow_left₀ hr0.le hr01 4
    norm_num at h4
    linarith
  have hLpos : 0 < -Real.log delta := by
    have := Real.log_neg hdelta hdlt1
    linarith
  have hspos : 0 < Real.sqrt (-Real.log delta) := Real.sqrt_pos.2 hLpos
  have hlower := (Zdelta_bounds hr0 hr01 hdelta hle).1
  have hpos : 0 < (-Real.log delta) * Real.sqrt (-Real.log delta)
      / (6 * Real.sqrt 2 * Real.pi) := by positivity
  linarith

/-- The profile is even, as Move 1 requires. -/
theorem profile_even (r0 delta t : ℝ) (r : ℝ) :
    profile r0 delta t (-r) = profile r0 delta t r := by
  simp only [profile, logWeight, abs_neg]

/-- The profile is bounded on the whole line by its value at the inner radius. This
is the concrete discharge of the `phi ∈ L²` requirement: for fixed `δ > 0` the
competitor is a bounded function supported in a set of finite measure. -/
theorem profile_abs_le {r0 delta : ℝ} (hsq : 0 < Real.sqrt delta)
    (hle : Real.sqrt delta ≤ r0) (hr01 : r0 < 1) (t r : ℝ) :
    |profile r0 delta t r|
      ≤ |t| * (Real.sqrt (-Real.log (Real.sqrt delta)) / Real.sqrt delta) := by
  have hsq1 : Real.sqrt delta < 1 := lt_of_le_of_lt hle hr01
  have hlogsq : 0 < -Real.log (Real.sqrt delta) := by
    have := Real.log_neg hsq hsq1
    linarith
  have hbound : 0 ≤ Real.sqrt (-Real.log (Real.sqrt delta)) / Real.sqrt delta := by
    positivity
  by_cases hr : Real.sqrt delta ≤ |r| ∧ |r| ≤ r0
  · have hrpos : 0 < |r| := lt_of_lt_of_le hsq hr.1
    have hrlt : |r| < 1 := lt_of_le_of_lt hr.2 hr01
    have hlogr : 0 < -Real.log |r| := by
      have := Real.log_neg hrpos hrlt
      linarith
    have hwnn : 0 ≤ Real.sqrt (-Real.log |r|) / |r| := by positivity
    have hmono := logWeight_antitone hsq hr.1 hrlt
    simp only [profile, if_pos hr, logWeight, abs_mul, abs_of_nonneg hwnn]
    exact mul_le_mul_of_nonneg_left hmono (abs_nonneg t)
  · simp only [profile, if_neg hr, abs_zero]
    exact mul_nonneg (abs_nonneg t) hbound

end Manhattan.V4.Frequency
