import Manhattan.V4.Frequency.FixedFrequency

/-!
# Version 4, Move 3: the frequency integration

The Version 4 fixed-frequency bound is

  `r_λ(p) ≤ C / (λ + a(p)² (1 + log₊(1/(√λ + a(p))))^{3/2})`,   `a(p) = max(|p₁|,|p₂|)`.

This file shows it is integrable over the torus uniformly in `λ ∈ (0,1]`, in two steps.

* `annulusIntegral_le_two` is the scalar integral that produces the finiteness:
  `∫_ε^{r₀} dx / (x (1 + log(1/x))^{3/2}) ≤ 2`, uniformly in `ε > 0`. Its
  antiderivative is `2 (1 + log(1/x))^{-1/2}`, and the bound is uniform because that
  antiderivative is bounded at the outer endpoint and nonnegative at the inner one.
  This is the square-annulus half of Move 3; the small-square half is the `1/λ` bound
  against a square of area `≍ λ`.
* `v4Majorant_le_frequencyMajorant` shows the Version 4 majorant is pointwise below
  the manuscript's sealed `Operator.frequencyMajorant`, so the whole three-region
  integration of `Manhattan/Estimates/Regional.lean` applies verbatim. That is what
  `regionalIntegralBoundsOfV4Bound` records: the Version 4 fixed-frequency bound is
  by itself enough to construct `Operator.RegionalIntegralBounds`, hence the uniform
  Green bound.

Note the comparison needs no case distinction at `a(p) ≤ √λ` and no hypothesis on
`sin p₁`: the `λ` carried by the Version 4 denominator dominates the driftless entry
of the manuscript's majorant on its own.
-/

noncomputable section

namespace Manhattan.V4.Frequency

open MeasureTheory

/-! ### The scalar integral -/

/-- The Version 4 scalar annulus kernel `1 / (x (1 + log(1/x))^{3/2})`. -/
def annulusKernel (x : ℝ) : ℝ := (x * Real.sqrt (1 - Real.log x) ^ 3)⁻¹

theorem annulusKernel_hasDerivAt {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    HasDerivAt (fun y : ℝ => 2 * (Real.sqrt (1 - Real.log y))⁻¹) (annulusKernel x) x := by
  have hpos : 0 < 1 - Real.log x := by
    have := Real.log_nonpos hx.le hx1
    linarith
  have hinner : HasDerivAt (fun y => 1 - Real.log y) (-1 / x) x := by
    convert (hasDerivAt_const x 1).sub (Real.hasDerivAt_log hx.ne') using 1
    ring
  have hsqrt := hinner.sqrt hpos.ne'
  have hinv := hsqrt.inv (Real.sqrt_pos.2 hpos).ne'
  convert hinv.const_mul 2 using 1
  unfold annulusKernel
  field_simp [(Real.sqrt_pos.2 hpos).ne']

/-- The scalar integral of Move 3, uniformly bounded down to the origin:
`∫_ε^{r₀} dx / (x (1 + log(1/x))^{3/2}) ≤ 2`. This is the integral that produces the
finiteness of the frequency integral. -/
theorem annulusIntegral_le_two {r0 eps : ℝ} (heps : 0 < eps) (hle : eps ≤ r0)
    (hr0 : r0 ≤ 1) : (∫ x in eps..r0, annulusKernel x) ≤ 2 := by
  have hderiv : ∀ x ∈ Set.uIcc eps r0,
      HasDerivAt (fun y : ℝ => 2 * (Real.sqrt (1 - Real.log y))⁻¹) (annulusKernel x) x := by
    intro x hx
    rw [Set.uIcc_of_le hle] at hx
    exact annulusKernel_hasDerivAt (heps.trans_le hx.1) (hx.2.trans hr0)
  have hint : IntervalIntegrable annulusKernel volume eps r0 := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le hle] at hx
    have hxPos := heps.trans_le hx.1
    have hlogPos : 0 < 1 - Real.log x := by
      have := Real.log_nonpos hxPos.le (hx.2.trans hr0)
      linarith
    apply ContinuousAt.continuousWithinAt
    unfold annulusKernel
    apply ContinuousAt.inv₀
    · apply ContinuousAt.mul continuousAt_id
      apply ContinuousAt.pow
      apply ContinuousAt.sqrt
      exact continuousAt_const.sub (Real.continuousAt_log hxPos.ne')
    · exact mul_ne_zero hxPos.ne' (pow_ne_zero 3 (Real.sqrt_pos.2 hlogPos).ne')
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have hleftNonneg : 0 ≤ 2 * (Real.sqrt (1 - Real.log eps))⁻¹ := by positivity
  have hlogr0 : 1 ≤ 1 - Real.log r0 := by
    have := Real.log_nonpos (heps.trans_le hle).le hr0
    linarith
  have hsqrt1 : 1 ≤ Real.sqrt (1 - Real.log r0) := by
    have := Real.sqrt_le_sqrt hlogr0
    simpa using this
  have hsqrtpos : 0 < Real.sqrt (1 - Real.log r0) := lt_of_lt_of_le one_pos hsqrt1
  have hcancel : (Real.sqrt (1 - Real.log r0))⁻¹ * Real.sqrt (1 - Real.log r0) = 1 :=
    inv_mul_cancel₀ hsqrtpos.ne'
  have hinvpos : 0 < (Real.sqrt (1 - Real.log r0))⁻¹ := inv_pos.2 hsqrtpos
  have hinv1 : (Real.sqrt (1 - Real.log r0))⁻¹ ≤ 1 := by nlinarith [hcancel, hinvpos, hsqrt1]
  linarith

/-! ### The Version 4 majorant dominates the manuscript's majorant -/

/-- The Version 4 fixed-frequency majorant (3) is pointwise below the manuscript's
`Operator.frequencyMajorant`, for every frequency and every `λ > 0`. No case
distinction at `a(p) ≤ √λ` and no hypothesis on `sin p₁` is needed. -/
theorem v4Majorant_le_frequencyMajorant {r0 lambda : ℝ} (hr0 : 0 < r0) (hr01 : r0 ≤ 1)
    (hlambda : 0 < lambda) (p : Fin 2 → ℝ) :
    v4Majorant lambda p ≤ Operator.frequencyMajorant r0 lambda p := by
  have hLam1 : 1 ≤ v4LogScale lambda p ^ (3 / 2 : ℝ) := one_le_v4LogScale_rpow lambda p
  have hann : 0 ≤ Operator.maxFrequency p ^ 2 := sq_nonneg _
  have hEpos : 0 < lambda + Operator.maxFrequency p ^ 2 * v4LogScale lambda p ^ (3 / 2 : ℝ) :=
    v4Majorant_denom_pos hlambda p
  have hthetann : 0 ≤ Operator.theta p := by
    rw [Manhattan.Estimates.operator_theta_eq]
    exact Manhattan.Estimates.theta_nonneg p
  have hdriftless : v4Majorant lambda p ≤ Operator.driftlessMajorant lambda p := by
    unfold v4Majorant Operator.driftlessMajorant
    have hpos : 0 < lambda + Operator.theta p := by linarith
    refine one_div_le_one_div_of_le hpos ?_
    have h1 : Operator.theta p ≤ Operator.maxFrequency p ^ 2 := theta_le_maxFrequency_sq p
    nlinarith [hann, hLam1]
  refine le_min hdriftless ?_
  unfold Operator.correctedMajorant
  split_ifs with hzero
  · exact hdriftless
  · have hapos : 0 < Operator.maxFrequency p ^ 2 :=
      pow_pos (lt_of_le_of_ne (maxFrequency_nonneg p) (Ne.symm hzero)) 2
    have hdpos : 0 < Real.sqrt lambda + Operator.maxFrequency p :=
      add_pos_of_pos_of_nonneg (Real.sqrt_pos.2 hlambda) (maxFrequency_nonneg p)
    have hratio : r0 / (Real.sqrt lambda + Operator.maxFrequency p)
        ≤ 1 / (Real.sqrt lambda + Operator.maxFrequency p) := by
      apply div_le_div_of_nonneg_right hr01 hdpos.le
    have hlogmono : Operator.logPos (r0 / (Real.sqrt lambda + Operator.maxFrequency p))
        ≤ Operator.logPos (1 / (Real.sqrt lambda + Operator.maxFrequency p)) :=
      logPos_mono (by positivity) hratio
    have hscale : Operator.frequencyLogScale r0 lambda p ≤ v4LogScale lambda p := by
      unfold Operator.frequencyLogScale v4LogScale
      linarith
    have hscale1 : 1 ≤ Operator.frequencyLogScale r0 lambda p := by
      have := logPos_nonneg (r0 / (Real.sqrt lambda + Operator.maxFrequency p))
      unfold Operator.frequencyLogScale
      linarith
    have hscalerp : Operator.frequencyLogScale r0 lambda p ^ (3 / 2 : ℝ)
        ≤ v4LogScale lambda p ^ (3 / 2 : ℝ) :=
      rpow_three_halves_mono (by linarith) hscale
    have hscalerp1 : 1 ≤ Operator.frequencyLogScale r0 lambda p ^ (3 / 2 : ℝ) :=
      one_le_rpow_three_halves hscale1
    unfold v4Majorant
    refine one_div_le_one_div_of_le (by positivity) ?_
    nlinarith [hapos, hscalerp, hlambda]

/-! ### The frequency integral -/

/-- MOVE 3, frequency integration. A density dominated by the Version 4
fixed-frequency majorant satisfies the three regional bounds of
`Manhattan/Estimates/Regional.lean`, uniformly in `λ ∈ (0,1]`. The three regions are
the small square `a(p) ≤ √λ`, where the `1/λ` bound meets an area `≍ λ`; the square
annulus, where the scalar integral `annulusIntegral_le_two` is used; and the outer
region, where the dispersion is bounded below. -/
def regionalIntegralBoundsOfV4Bound
    (green : ℝ → ℝ) (density : ℝ → ℝ × ℝ → ℝ) (r0 C : ℝ)
    (hr0 : 0 < r0) (hr0One : r0 < 1) (hC : 0 ≤ C)
    (hdensityMeas : ∀ lambda, Measurable (density lambda))
    (hdensityNonneg : ∀ lambda z, 0 ≤ density lambda z)
    (hgreen : ∀ lambda, 0 < lambda → lambda ≤ 1 →
      green lambda ≤ Manhattan.Estimates.normalizedFrequencyIntegral (density lambda))
    (hpoint : ∀ lambda, 0 < lambda → lambda ≤ 1 → ∀ z : ℝ × ℝ,
      z.1 ∈ Manhattan.Estimates.torus → z.2 ∈ Manhattan.Estimates.torus →
      density lambda z ≤ C * v4Majorant lambda ![z.1, z.2]) :
    Operator.RegionalIntegralBounds green :=
  Manhattan.Estimates.regionalIntegralBoundsOfFrequencyBound green density r0 C hr0 hr0One hC
    hdensityMeas hdensityNonneg hgreen
    (fun lambda hl hl1 z hz1 hz2 =>
      (hpoint lambda hl hl1 z hz1 hz2).trans
        (mul_le_mul_of_nonneg_left
          (v4Majorant_le_frequencyMajorant hr0 hr0One.le hl _) hC))

/-- The uniform-in-`λ` Green bound produced by the Version 4 fixed-frequency bound.
The right-hand side does not depend on `λ`. -/
theorem uniform_green_bound_of_v4Bound
    (green : ℝ → ℝ) (density : ℝ → ℝ × ℝ → ℝ) (r0 C : ℝ)
    (hr0 : 0 < r0) (hr0One : r0 < 1) (hC : 0 ≤ C)
    (hdensityMeas : ∀ lambda, Measurable (density lambda))
    (hdensityNonneg : ∀ lambda z, 0 ≤ density lambda z)
    (hgreen : ∀ lambda, 0 < lambda → lambda ≤ 1 →
      green lambda ≤ Manhattan.Estimates.normalizedFrequencyIntegral (density lambda))
    (hpoint : ∀ lambda, 0 < lambda → lambda ≤ 1 → ∀ z : ℝ × ℝ,
      z.1 ∈ Manhattan.Estimates.torus → z.2 ∈ Manhattan.Estimates.torus →
      density lambda z ≤ C * v4Majorant lambda ![z.1, z.2])
    {lambda : ℝ} (hlambda : 0 < lambda) (hlambda1 : lambda ≤ 1) :
    green lambda ≤ C + 2 * (8 * C) + C * (2 * Real.pi ^ 2 / r0 ^ 2) :=
  Operator.uniform_green_bound_of_regional_bounds
    (regionalIntegralBoundsOfV4Bound green density r0 C hr0 hr0One hC
      hdensityMeas hdensityNonneg hgreen hpoint) hlambda hlambda1

end Manhattan.V4.Frequency
