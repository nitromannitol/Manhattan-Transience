import Manhattan.V4.Frequency.Integration
import Manhattan.Glue.Assembly
import Manhattan.Glue.Competitor
import Manhattan.Glue.LowLog

/-!
# Version 4, Move 3: the complementary region, and the route to Theorem 1.2

Move 3 (`Manhattan.V4.Frequency.move3_bound`) is proved on the
improvement region `√λ + a(p) ≤ r₀⁴`, and the frequency integration
(`regionalIntegralBoundsOfV4Bound`, `uniform_green_bound_of_v4Bound`) for a
density dominated everywhere by the Version 4 majorant.  It left one case split
open: the complementary region.  This file closes it and then composes the whole
Version 4 chain.

* `driftlessMajorant_le_v4Majorant` is the missing case.  On
  `√λ + a(p) > r₀⁴` the Version 4 logarithmic scale is bounded,
  `Λ ≤ 1 + 4 log(1/r₀)` (`v4LogScale_le_of_big`), and on the torus
  `θ(p) ≥ 2 a(p)²/π²` (`Manhattan.Estimates.dispersion_quadratic_bounds`), so the
  `g = 0` bound `r_λ(p) ≤ 1/(λ + θ(p))` already implies the Version 4 majorant
  with the constant `outerRegionConstant r₀ = max 1 ((1 + 4 log(1/r₀))^{3/2} π²/2)`,
  which depends only on `r₀`.

* `V4FrequencyBound` is the Version 4 analogue of Proposition 2.2 for the
  concrete model, and `v4FrequencyBound_of_move2Supply` assembles it from the
  two regions.  The existential over `s` in `V4Move2Supply` is what absorbs the
  axis swap.

* `annealedGreenBound_of_v4FrequencyBound` and `theorem_1_1_of_v4FrequencyBound`
  are the Version 4 route to the two frozen statements.  They go through
  `Manhattan.Glue.concreteGreenDensity_eq_resolventQuadratic`,
  `regionalIntegralBoundsOfV4Bound` and
  `Manhattan.Glue.annealedGreenBound_of_regional_identity`, so the competitor
  existential of `Manhattan.Operator.CompetitorBoundClaimV2` never appears: the
  Version 4 route bounds the resolvent quadratic form directly.  The frozen
  declarations are untouched and still proved by the existing development.
-/

noncomputable section

namespace Manhattan.V4.Frequency

open MeasureTheory
open scoped ENNReal

/-- The constant of the complementary region `√λ + a(p) > r₀⁴`, where the
Version 4 logarithmic scale is bounded by `1 + 4 log(1/r₀)`. -/
def outerRegionConstant (r0 : ℝ) : ℝ :=
  max 1 ((1 + 4 * Real.log (1 / r0)) ^ (3 / 2 : ℝ) * Real.pi ^ 2 / 2)

theorem one_le_outerRegionConstant (r0 : ℝ) : 1 ≤ outerRegionConstant r0 :=
  le_max_left _ _

theorem outerRegionConstant_pos (r0 : ℝ) : 0 < outerRegionConstant r0 :=
  lt_of_lt_of_le one_pos (one_le_outerRegionConstant r0)

/-- On the complementary region the Version 4 logarithmic scale is bounded by
the constant `1 + 4 log(1/r₀)`. -/
theorem v4LogScale_le_of_big {r0 lambda : ℝ} {p : Fin 2 → ℝ}
    (hr0 : 0 < r0) (hr01 : r0 ≤ 1 / 4) (hlambda : 0 < lambda)
    (hbig : r0 ^ 4 < Real.sqrt lambda + Operator.maxFrequency p) :
    v4LogScale lambda p ≤ 1 + 4 * Real.log (1 / r0) := by
  have hdpos : 0 < Real.sqrt lambda + Operator.maxFrequency p :=
    add_pos_of_pos_of_nonneg (Real.sqrt_pos.2 hlambda) (maxFrequency_nonneg p)
  have hr0pow : (0:ℝ) < r0 ^ 4 := by positivity
  have hlog : Real.log (1 / (Real.sqrt lambda + Operator.maxFrequency p))
      ≤ 4 * Real.log (1 / r0) := by
    have hle : 1 / (Real.sqrt lambda + Operator.maxFrequency p) ≤ 1 / r0 ^ 4 := by
      apply one_div_le_one_div_of_le hr0pow hbig.le
    have h1 : Real.log (1 / (Real.sqrt lambda + Operator.maxFrequency p))
        ≤ Real.log (1 / r0 ^ 4) := Real.log_le_log (by positivity) hle
    have h2 : Real.log (1 / r0 ^ 4) = 4 * Real.log (1 / r0) := by
      rw [one_div, one_div, Real.log_inv, Real.log_inv, Real.log_pow]
      push_cast
      ring
    linarith [h1, h2.le, h2.ge]
  have hlogr0 : 0 ≤ Real.log (1 / r0) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hr0]
    linarith
  have hpos : Operator.logPos (1 / (Real.sqrt lambda + Operator.maxFrequency p))
      ≤ 4 * Real.log (1 / r0) := by
    unfold Operator.logPos
    exact max_le hlog (by linarith)
  unfold v4LogScale
  linarith

/-- **The `g = 0` branch of the case split V4-B left open.**  On the region
`√λ + a(p) > r₀⁴` the driftless bound `1/(λ + θ(p))` already implies the
Version 4 majorant, with a constant depending only on `r₀`.  The two inputs are
the boundedness of the logarithmic scale there and `θ(p) ≥ 2 a(p)²/π²`. -/
theorem driftlessMajorant_le_v4Majorant {r0 lambda : ℝ} {p : Fin 2 → ℝ}
    (hr0 : 0 < r0) (hr01 : r0 ≤ 1 / 4) (hlambda : 0 < lambda)
    (hp0 : |p 0| ≤ Real.pi) (hp1 : |p 1| ≤ Real.pi)
    (hbig : r0 ^ 4 < Real.sqrt lambda + Operator.maxFrequency p) :
    Operator.driftlessMajorant lambda p
      ≤ outerRegionConstant r0 * v4Majorant lambda p := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  set L0 : ℝ := 1 + 4 * Real.log (1 / r0) with hL0def
  have hlogr0 : 0 ≤ Real.log (1 / r0) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hr0]
    linarith
  have hL0one : (1:ℝ) ≤ L0 := by simp only [hL0def]; linarith
  have hscale := v4LogScale_le_of_big hr0 hr01 hlambda hbig
  have hrpow : v4LogScale lambda p ^ (3 / 2 : ℝ) ≤ L0 ^ (3 / 2 : ℝ) :=
    rpow_three_halves_mono (by linarith [one_le_v4LogScale lambda p]) hscale
  have hL0rpow : (1:ℝ) ≤ L0 ^ (3 / 2 : ℝ) := one_le_rpow_three_halves hL0one
  -- `θ(p) ≥ 2 a(p)²/π²`
  have hd0 := (Manhattan.Estimates.dispersion_quadratic_bounds hp0).1
  have hd1 := (Manhattan.Estimates.dispersion_quadratic_bounds hp1).1
  have hd0n := Manhattan.Estimates.dispersion_nonneg (p 0)
  have hd1n := Manhattan.Estimates.dispersion_nonneg (p 1)
  have htheta : Operator.theta p
      = Manhattan.Estimates.dispersion (p 0) + Manhattan.Estimates.dispersion (p 1) := by
    rw [Manhattan.Estimates.operator_theta_eq]
    rfl
  have hlow : 2 * Operator.maxFrequency p ^ 2 / Real.pi ^ 2 ≤ Operator.theta p := by
    rw [htheta]
    unfold Operator.maxFrequency
    rcases le_total |p 1| |p 0| with h | h
    · have hm : max |p 0| |p 1| = |p 0| := max_eq_left h
      rw [hm, sq_abs]
      linarith
    · have hm : max |p 0| |p 1| = |p 1| := max_eq_right h
      rw [hm, sq_abs]
      linarith
  have hthetann : 0 ≤ Operator.theta p := by rw [htheta]; linarith
  have hK : (1:ℝ) ≤ outerRegionConstant r0 := one_le_outerRegionConstant r0
  have hKge : L0 ^ (3 / 2 : ℝ) * Real.pi ^ 2 / 2 ≤ outerRegionConstant r0 :=
    le_max_right _ _
  have hann : 0 ≤ Operator.maxFrequency p ^ 2 := sq_nonneg _
  have hkey : lambda + Operator.maxFrequency p ^ 2 * v4LogScale lambda p ^ (3 / 2 : ℝ)
      ≤ outerRegionConstant r0 * (lambda + Operator.theta p) := by
    have h1 : Operator.maxFrequency p ^ 2 * v4LogScale lambda p ^ (3 / 2 : ℝ)
        ≤ Operator.maxFrequency p ^ 2 * L0 ^ (3 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left hrpow hann
    have hfac : (0:ℝ) ≤ L0 ^ (3 / 2 : ℝ) * Real.pi ^ 2 / 2 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hlow hfac
    have h2 : Operator.maxFrequency p ^ 2 * L0 ^ (3 / 2 : ℝ)
        ≤ (L0 ^ (3 / 2 : ℝ) * Real.pi ^ 2 / 2) * Operator.theta p := by
      have hid : (L0 ^ (3 / 2 : ℝ) * Real.pi ^ 2 / 2)
            * (2 * Operator.maxFrequency p ^ 2 / Real.pi ^ 2)
          = Operator.maxFrequency p ^ 2 * L0 ^ (3 / 2 : ℝ) := by
        field_simp
      rw [← hid]
      exact hmul
    have h3 : (L0 ^ (3 / 2 : ℝ) * Real.pi ^ 2 / 2) * Operator.theta p
        ≤ outerRegionConstant r0 * Operator.theta p :=
      mul_le_mul_of_nonneg_right hKge hthetann
    have h4 : lambda ≤ outerRegionConstant r0 * lambda :=
      le_mul_of_one_le_left hlambda.le hK
    have hexp : outerRegionConstant r0 * (lambda + Operator.theta p)
        = outerRegionConstant r0 * lambda + outerRegionConstant r0 * Operator.theta p := by
      ring
    rw [hexp]
    linarith
  have hEpos : 0 < lambda + Operator.maxFrequency p ^ 2 * v4LogScale lambda p ^ (3 / 2 : ℝ) :=
    v4Majorant_denom_pos hlambda p
  have hDpos : 0 < lambda + Operator.theta p := by linarith
  unfold Operator.driftlessMajorant v4Majorant
  rw [mul_one_div, div_le_div_iff₀ hDpos hEpos]
  linarith [hkey]

/-! ## The Version 4 fixed-frequency bound, and the route to Theorem 1.2 -/

/-- **The Version 4 fixed-frequency bound for the concrete model.**  This is the
Version 4 analogue of the manuscript's Proposition 2.2: the resolvent quadratic
form at the constant Walsh vector is dominated by `C` times the Version 4
majorant `1/(λ + a(p)²(1 + log₊(1/(√λ + a(p))))^{3/2})`, at every torus
frequency and uniformly in `λ ∈ (0,1]`. -/
def V4FrequencyBound (C : ℝ) : Prop :=
  ∀ (lambda : ℝ), ∀ hlambda : 0 < lambda, lambda ≤ 1 → ∀ p : Fin 2 → ℝ,
    p 0 ∈ Manhattan.Estimates.torus → p 1 ∈ Manhattan.Estimates.torus →
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).resolventQuadratic
        hlambda (Manhattan.walshL2 ∅) ≤ C * v4Majorant lambda p

/-- **The output of Move 2 in the improvement region.**  For each frequency with
`√λ + a(p) ≤ r₀⁴` the competitor construction supplies the closed form
`1/(h₀ + s² Z_δ/C)` for some `s` obeying Jordan's inequality `(2/π)² a(p)² ≤ s²`.
The existential over `s` is what absorbs the axis swap: on the horizontal branch
`s = sin p₁` and on the vertical branch `s = sin p₂`. -/
def V4Move2Supply (r0 C : ℝ) : Prop :=
  ∀ (lambda : ℝ), ∀ hlambda : 0 < lambda, lambda ≤ 1 → ∀ p : Fin 2 → ℝ,
    p 0 ∈ Manhattan.Estimates.torus → p 1 ∈ Manhattan.Estimates.torus →
    Real.sqrt lambda + Operator.maxFrequency p ≤ r0 ^ 4 →
    ∃ s : ℝ, (2 / Real.pi) ^ 2 * Operator.maxFrequency p ^ 2 ≤ s ^ 2 ∧
      (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).resolventQuadratic
          hlambda (Manhattan.walshL2 ∅)
        ≤ 1 / (lambda + Operator.theta p
            + s ^ 2 * Zdelta r0 (Real.sqrt lambda + Operator.maxFrequency p) / C)

/-- **The case split V4-B left open, closed.**  Move 3 covers the improvement
region `√λ + a(p) ≤ r₀⁴`; the `g = 0` bound covers its complement.  The composed
constant is the maximum of the two. -/
theorem v4FrequencyBound_of_move2Supply {r0 C : ℝ}
    (hr0 : 0 < r0) (hr01 : r0 ≤ 1 / 4) (hC : 0 < C)
    (hsupply : V4Move2Supply r0 C) :
    V4FrequencyBound (max (max 1 (8 * Real.pi ^ 3 * C)) (outerRegionConstant r0)) := by
  intro lambda hlambda hlambda1 p hp0 hp1
  have hp0abs : |p 0| ≤ Real.pi := abs_le.2 ⟨hp0.1.le, hp0.2⟩
  have hp1abs : |p 1| ≤ Real.pi := abs_le.2 ⟨hp1.1.le, hp1.2⟩
  have hmpos : 0 ≤ v4Majorant lambda p := (v4Majorant_pos hlambda p).le
  rcases le_or_gt (Real.sqrt lambda + Operator.maxFrequency p) (r0 ^ 4) with hle | hgt
  · obtain ⟨s, hs, hmove2⟩ := hsupply lambda hlambda hlambda1 p hp0 hp1 hle
    have h := move3_bound hr0 hr01 hlambda hC hs hle hmove2
    refine h.trans (mul_le_mul_of_nonneg_right ?_ hmpos)
    exact le_max_left _ _
  · have hdrift := Manhattan.Glue.concrete_resolventQuadratic_le_driftless hlambda p
    have houter := driftlessMajorant_le_v4Majorant hr0 hr01 hlambda hp0abs hp1abs hgt
    refine (hdrift.trans houter).trans (mul_le_mul_of_nonneg_right ?_ hmpos)
    exact le_max_right _ _

/-- **The complementary region, verified for the concrete model.**  Outside the
improvement region the Version 4 fixed-frequency bound holds unconditionally,
with the constant `outerRegionConstant r₀`.  This is the half of
`V4FrequencyBound` that needs no competitor. -/
theorem resolventQuadratic_le_v4Majorant_outer {r0 lambda : ℝ} {p : Fin 2 → ℝ}
    (hr0 : 0 < r0) (hr01 : r0 ≤ 1 / 4) (hlambda : 0 < lambda)
    (hp0 : p 0 ∈ Manhattan.Estimates.torus) (hp1 : p 1 ∈ Manhattan.Estimates.torus)
    (hbig : r0 ^ 4 < Real.sqrt lambda + Operator.maxFrequency p) :
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).resolventQuadratic
        hlambda (Manhattan.walshL2 ∅)
      ≤ outerRegionConstant r0 * v4Majorant lambda p :=
  (Manhattan.Glue.concrete_resolventQuadratic_le_driftless hlambda p).trans
    (driftlessMajorant_le_v4Majorant hr0 hr01 hlambda
      (abs_le.2 ⟨hp0.1.le, hp0.2⟩) (abs_le.2 ⟨hp1.1.le, hp1.2⟩) hbig)

/-- **The Version 4 uniform Green bound.**  The right-hand side does not depend
on `λ`; this is Move 3's frequency integration applied to the concrete Green
density. -/
theorem uniform_green_bound_of_v4FrequencyBound {C : ℝ} (hC : 0 ≤ C)
    (h : V4FrequencyBound C) {lambda : ℝ} (hlambda : 0 < lambda) (hlambda1 : lambda ≤ 1) :
    Manhattan.Estimates.normalizedFrequencyIntegral
        (Manhattan.Glue.concreteGreenDensity lambda)
      ≤ C + 2 * (8 * C) + C * (2 * Real.pi ^ 2 / (1 / 2 : ℝ) ^ 2) :=
  uniform_green_bound_of_v4Bound
    (fun l => Manhattan.Estimates.normalizedFrequencyIntegral
      (Manhattan.Glue.concreteGreenDensity l))
    Manhattan.Glue.concreteGreenDensity (1 / 2) C (by norm_num) (by norm_num) hC
    Manhattan.Glue.concreteGreenDensity_measurable
    Manhattan.Glue.concreteGreenDensity_nonneg
    (fun _ _ _ => le_rfl)
    (fun l hl hl1 z hz1 hz2 => by
      rw [Manhattan.Glue.concreteGreenDensity_eq_resolventQuadratic hl]
      exact h l hl hl1 (Manhattan.Glue.concreteFrequency z) hz1 hz2)
    hlambda hlambda1

/-- **The Version 4 route to Theorem 1.2.**  A fixed-frequency bound by the
Version 4 majorant is by itself enough for the annealed Green bound: the
three-region integration of `Manhattan/Estimates/Regional.lean` applies through
`v4Majorant_le_frequencyMajorant`, and `Manhattan.Glue.concreteGreenIdentity` is
the model identity. -/
theorem annealedGreenBound_of_v4FrequencyBound {C : ℝ} (hC : 0 ≤ C)
    (h : V4FrequencyBound C) : Manhattan.AnnealedGreenBound :=
  Manhattan.Glue.annealedGreenBound_of_regional_identity
    (fun l => Manhattan.Estimates.normalizedFrequencyIntegral
      (Manhattan.Glue.concreteGreenDensity l))
    (regionalIntegralBoundsOfV4Bound
      (fun l => Manhattan.Estimates.normalizedFrequencyIntegral
        (Manhattan.Glue.concreteGreenDensity l))
      Manhattan.Glue.concreteGreenDensity (1 / 2) C (by norm_num) (by norm_num) hC
      Manhattan.Glue.concreteGreenDensity_measurable
      Manhattan.Glue.concreteGreenDensity_nonneg
      (fun _ _ _ => le_rfl)
      (fun l hl hl1 z hz1 hz2 => by
        rw [Manhattan.Glue.concreteGreenDensity_eq_resolventQuadratic hl]
        exact h l hl hl1 (Manhattan.Glue.concreteFrequency z) hz1 hz2))
    Manhattan.Glue.concreteGreenIdentity

/-- **The Version 4 route to the statement of Theorem 1.1.**  Quenched
finiteness of the Green series, obtained from the Version 4 fixed-frequency
bound through the annealed bound and the Model part's subordination argument. -/
theorem theorem_1_1_of_v4FrequencyBound {C : ℝ} (hC : 0 ≤ C)
    (h : V4FrequencyBound C) :
    ∀ᵐ omega ∂Manhattan.environmentLaw,
      ∀ x : Manhattan.Site, Manhattan.discreteGreen omega x < ∞ :=
  Manhattan.theorem_1_1 (annealedGreenBound_of_v4FrequencyBound hC h)

/-- The composed Version 4 route, from the Move 2 supply straight to Theorem
1.1's statement. -/
theorem theorem_1_1_of_v4Move2Supply {r0 C : ℝ}
    (hr0 : 0 < r0) (hr01 : r0 ≤ 1 / 4) (hC : 0 < C)
    (hsupply : V4Move2Supply r0 C) :
    ∀ᵐ omega ∂Manhattan.environmentLaw,
      ∀ x : Manhattan.Site, Manhattan.discreteGreen omega x < ∞ :=
  theorem_1_1_of_v4FrequencyBound
    (zero_le_one.trans ((le_max_left 1 _).trans (le_max_left _ _)))
    (v4FrequencyBound_of_move2Supply hr0 hr01 hC hsupply)

/-- The composed Version 4 route to Theorem 1.2. -/
theorem annealedGreenBound_of_v4Move2Supply {r0 C : ℝ}
    (hr0 : 0 < r0) (hr01 : r0 ≤ 1 / 4) (hC : 0 < C)
    (hsupply : V4Move2Supply r0 C) : Manhattan.AnnealedGreenBound :=
  annealedGreenBound_of_v4FrequencyBound
    (zero_le_one.trans ((le_max_left 1 _).trans (le_max_left _ _)))
    (v4FrequencyBound_of_move2Supply hr0 hr01 hC hsupply)

end Manhattan.V4.Frequency
