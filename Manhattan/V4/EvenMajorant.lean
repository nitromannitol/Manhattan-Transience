import Manhattan.Glue.ProjectionDischarge
import Manhattan.Glue.CubicDischargeTorus

/-!
# Version 4, Step 2: the even majorant `M` and the majorization of the multiplier

Version 4 of the argument (Steps 2--3 and the
`VERSION 4` section) replaces the multiplier `M(P)` of the manuscript's (35) by
the **separately even** majorant

  `M(r,r',β) = κ (δ + |r| + |r'| + |β|)`,      `δ = √λ + a`.

Everything that the parity construction needs from `M` is that it is positive,
symmetric in the two row frequencies, and **even in each variable separately**;
the majorization proved here is what connects it to the operator estimate that
the existing development already contains.

## What is proved

* `Manhattan.V4.torusAbs`, the distance to `2πℤ`, written as `|·|` of the
  reduction to the fundamental domain `(-π,π]`.  On `(-π,π]` it *is* `|·|`
  (`torusAbs_eq_abs`), so `evenMajorant` is literally the note's `M` on the
  fundamental domain, but it is genuinely `2π`-periodic and even, which the
  bare `|·|` is not.  Both properties are used by the parity construction:
  evenness for the four cancellations, periodicity for the translation in the
  row frequency that identifies `(I-Π)K`.
* `Manhattan.V4.multiplier_le_evenMajorant`: the **majorization**

    `Estimates.multiplier 40 q (β, r+r'-p₂)  ≤  evenMajorant 120 δ r r' β`

  whenever `λ ≤ δ` and `|p₂| ≤ δ`.  The two inputs are `2|sin(x/2)| ≤ |x|`
  (applied to the fundamental representative, which is where `torusAbs`
  enters) and `|α|_𝕋 ≤ |r| + |r'| + |p₂|`.  The constant is `κ = 120 = 3·40`.
* `Manhattan.V4.rawMultiplierEnergy_le_evenMajorantEnergy`: the integrated
  form, `∫ multiplier |k|² ≤ ∫ M |k|²` for every bounded measurable raw
  type-`112` kernel.

## Why the order of the two steps matters

The operator estimate (OP) of the note is obtained from the existing
development by composing

  `‖Π K‖₊² + ‖D₃ (Π K)‖₋²  ≤  5 ∑ ∫ multiplier |Π K|²`
      (`Manhattan.Glue.tsum_integral_inv_symbolWeight_degreeRaiseDir_le`
       together with `Estimates.fourEstimateCore_le_multiplier` and the
       transport of `Manhattan/Glue/Transport.lean`)
  `                        ≤  5 ∑ ∫ multiplier |K|²`
      (the input-projection contraction, `Manhattan/Glue/OrderedContractivity.lean`
       and `Manhattan.Glue.multiplier_integral_type112DiagonalProjection_le`)
  `                        ≤  5 ∑ ∫ M |K|²`
      (this file).

**The projection contraction is applied with the TRUE total-frequency
multiplier, and only then is the weight enlarged to `M`.**  That is why no
commutation of `Π` with `M` is ever needed: `M` is not a function of the total
frequency `P = (β, α)` alone -- it depends on `r` and `r'` separately -- so it
does *not* commute with `Π`, and the enlargement is a pointwise inequality
under a fixed integral, performed after every operator step is finished.

Paper: `manuscript.tex:983-987` (`eq:M` = (35)), `manuscript.tex:1193-1198`
(equation (46)); ERRATA E-010 / for the multiplier's failure to be
a trigonometric polynomial.
-/

open MeasureTheory

namespace Manhattan.V4

noncomputable section

/-! ## The distance to `2πℤ` -/

/-- The distance from `x` to `2πℤ`: the ordinary absolute value of the
reduction of `x` to the fundamental domain `(-π, π]`. -/
def torusAbs (x : ℝ) : ℝ := |Glue.torusWrap x|

theorem torusWrap_add_int_mul (x : ℝ) (n : ℤ) :
    Glue.torusWrap (x + (n : ℝ) * (2 * Real.pi)) = Glue.torusWrap x := by
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  unfold Glue.torusWrap
  have h : (x + (n : ℝ) * (2 * Real.pi) - Real.pi) / (2 * Real.pi)
      = (x - Real.pi) / (2 * Real.pi) + (n : ℝ) := by
    field_simp
    ring
  rw [h, Int.ceil_add_intCast]
  push_cast
  ring

/-- The canonical decomposition `x = torusWrap x + n·2π`. -/
theorem exists_torusWrap_decomposition (x : ℝ) :
    ∃ n : ℤ, x = Glue.torusWrap x + (n : ℝ) * (2 * Real.pi) := by
  refine ⟨⌈(x - Real.pi) / (2 * Real.pi)⌉, ?_⟩
  unfold Glue.torusWrap
  ring

theorem torusWrap_mem_torus (x : ℝ) : Glue.torusWrap x ∈ Estimates.torus := by
  have htwo : (0:ℝ) < 2 * Real.pi := by positivity
  set n : ℤ := ⌈(x - Real.pi) / (2 * Real.pi)⌉ with hn
  have h1 : (x - Real.pi) / (2 * Real.pi) ≤ (n : ℝ) := Int.le_ceil _
  have h2 : ((n : ℤ) : ℝ) - 1 < (x - Real.pi) / (2 * Real.pi) := by
    have h := Int.ceil_lt_add_one ((x - Real.pi) / (2 * Real.pi))
    rw [← hn] at h
    linarith
  have h1' : x - Real.pi ≤ (n : ℝ) * (2 * Real.pi) := (div_le_iff₀ htwo).mp h1
  have h2' : ((n : ℝ) - 1) * (2 * Real.pi) < x - Real.pi := (lt_div_iff₀ htwo).mp h2
  have hcomm : (n : ℝ) * (2 * Real.pi) = 2 * Real.pi * (n : ℝ) := by ring
  rw [hcomm] at h1'
  have hcomm2 : ((n : ℝ) - 1) * (2 * Real.pi) = 2 * Real.pi * (n : ℝ) - 2 * Real.pi := by ring
  rw [hcomm2] at h2'
  refine ⟨?_, ?_⟩
  · show -Real.pi < x - 2 * Real.pi * (n : ℝ)
    linarith
  · show x - 2 * Real.pi * (n : ℝ) ≤ Real.pi
    linarith

theorem torusAbs_nonneg (x : ℝ) : 0 ≤ torusAbs x := abs_nonneg _

theorem torusAbs_le_pi (x : ℝ) : torusAbs x ≤ Real.pi := by
  obtain ⟨h1, h2⟩ := torusWrap_mem_torus x
  rw [torusAbs, abs_le]
  exact ⟨by linarith, h2⟩

/-- On the fundamental domain the even majorant is literally the note's
`κ(δ + |r| + |r'| + |β|)`. -/
theorem torusAbs_eq_abs {x : ℝ} (hx : x ∈ Estimates.torus) : torusAbs x = |x| := by
  rw [torusAbs, Glue.torusWrap_eq_self hx]

theorem torusAbs_periodic : Function.Periodic torusAbs (2 * Real.pi) := by
  intro x
  rw [torusAbs, torusAbs, Glue.torusWrap_periodic]

theorem torusAbs_measurable : Measurable torusAbs := by
  have h : Measurable fun x : ℝ => ‖Glue.torusWrap x‖ := Glue.torusWrap_measurable.norm
  simpa [torusAbs, Real.norm_eq_abs] using h

/-- The distance to `2πℤ` is an even function.  This is the property the
parity construction uses. -/
theorem torusAbs_neg (x : ℝ) : torusAbs (-x) = torusAbs x := by
  obtain ⟨n, hn⟩ := exists_torusWrap_decomposition x
  have hneg : -x = -(Glue.torusWrap x) + ((-n : ℤ) : ℝ) * (2 * Real.pi) := by
    push_cast
    linarith
  have h1 : Glue.torusWrap (-x) = Glue.torusWrap (-(Glue.torusWrap x)) := by
    rw [hneg, torusWrap_add_int_mul]
  obtain ⟨hlow, hhigh⟩ := torusWrap_mem_torus x
  rcases eq_or_lt_of_le hhigh with heq | hlt
  · have hpi : Glue.torusWrap (-Real.pi) = Real.pi := by
      have hstep : (-Real.pi : ℝ) = Real.pi + ((-1 : ℤ) : ℝ) * (2 * Real.pi) := by
        push_cast; ring
      rw [hstep, torusWrap_add_int_mul,
        Glue.torusWrap_eq_self (x := Real.pi) ⟨by linarith [Real.pi_pos], le_refl _⟩]
    rw [torusAbs, torusAbs, h1, heq, hpi]
  · rw [torusAbs, torusAbs, h1,
      Glue.torusWrap_eq_self (x := -(Glue.torusWrap x)) ⟨by linarith, by linarith⟩,
      abs_neg]

/-! ## The two trigonometric inputs -/

/-- `2|sin(x/2)|` only sees `x` modulo `2π`, and is bounded by the absolute
value of every representative. -/
theorem two_abs_sin_half_le {x c : ℝ} {n : ℤ} (h : x = c + (n : ℝ) * (2 * Real.pi)) :
    2 * |Real.sin (x / 2)| ≤ |c| := by
  have hx : x / 2 = c / 2 + (n : ℝ) * Real.pi := by
    rw [h]; ring
  have habs : |((-1 : ℝ) ^ n)| = 1 := by
    rw [abs_zpow]
    norm_num
  have hsin : |Real.sin (x / 2)| = |Real.sin (c / 2)| := by
    rw [hx, Real.sin_add_int_mul_pi, abs_mul, habs, one_mul]
  have hbound : |Real.sin (c / 2)| ≤ |c / 2| := Real.abs_sin_le_abs
  rw [hsin]
  rw [abs_div] at hbound
  have h2 : |(2 : ℝ)| = 2 := by norm_num
  rw [h2] at hbound
  linarith

theorem two_abs_sin_half_le_torusAbs (x : ℝ) :
    2 * |Real.sin (x / 2)| ≤ torusAbs x := by
  obtain ⟨n, hn⟩ := exists_torusWrap_decomposition x
  exact two_abs_sin_half_le hn

theorem dispersion_le_two_abs_sin_half (x : ℝ) :
    Estimates.dispersion x ≤ 2 * |Real.sin (x / 2)| := by
  have hd : Estimates.dispersion x = 2 * Real.sin (x / 2) ^ 2 := by
    unfold Estimates.dispersion
    rw [show Real.cos x = Real.cos (2 * (x / 2)) by congr 1; ring, Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq (x / 2)]
  have hone : |Real.sin (x / 2)| ≤ 1 := Real.abs_sin_le_one _
  have hsq : Real.sin (x / 2) ^ 2 = |Real.sin (x / 2)| ^ 2 := (sq_abs _).symm
  rw [hd, hsq]
  nlinarith [abs_nonneg (Real.sin (x / 2))]

/-- The torus triangle inequality in the only form the majorization needs. -/
theorem abs_add_sub_le (a b c : ℝ) : |a + b - c| ≤ |a| + |b| + |c| := by
  have ha1 := neg_abs_le a
  have ha2 := le_abs_self a
  have hb1 := neg_abs_le b
  have hb2 := le_abs_self b
  have hc1 := neg_abs_le c
  have hc2 := le_abs_self c
  rw [abs_le]
  constructor <;> linarith

/-- The torus triangle inequality in the only form the majorization needs. -/
theorem two_abs_sin_half_mixedAlpha_le (r r' p₂ : ℝ) :
    2 * |Real.sin ((r + r' - p₂) / 2)| ≤ torusAbs r + torusAbs r' + |p₂| := by
  obtain ⟨n, hn⟩ := exists_torusWrap_decomposition r
  obtain ⟨n', hn'⟩ := exists_torusWrap_decomposition r'
  have hdec : r + r' - p₂ =
      (Glue.torusWrap r + Glue.torusWrap r' - p₂) + ((n + n' : ℤ) : ℝ) * (2 * Real.pi) := by
    push_cast
    linarith
  exact (two_abs_sin_half_le hdec).trans
    (abs_add_sub_le (Glue.torusWrap r) (Glue.torusWrap r') p₂)

/-! ## The even majorant -/

/-- The **even majorant** `M(r,r',β) = κ(δ + |r| + |r'| + |β|)` of the Version 4
rewrite, with `|·|` the distance to `2πℤ`. -/
def evenMajorant (kappa delta r r' beta : ℝ) : ℝ :=
  kappa * (delta + torusAbs r + torusAbs r' + torusAbs beta)

theorem evenMajorant_neg_row (kappa delta r r' beta : ℝ) :
    evenMajorant kappa delta (-r) r' beta = evenMajorant kappa delta r r' beta := by
  rw [evenMajorant, evenMajorant, torusAbs_neg]

theorem evenMajorant_neg_row' (kappa delta r r' beta : ℝ) :
    evenMajorant kappa delta r (-r') beta = evenMajorant kappa delta r r' beta := by
  rw [evenMajorant, evenMajorant, torusAbs_neg]

theorem evenMajorant_neg_col (kappa delta r r' beta : ℝ) :
    evenMajorant kappa delta r r' (-beta) = evenMajorant kappa delta r r' beta := by
  rw [evenMajorant, evenMajorant, torusAbs_neg]

/-- `M` is symmetric in the two row frequencies. -/
theorem evenMajorant_swap (kappa delta r r' beta : ℝ) :
    evenMajorant kappa delta r r' beta = evenMajorant kappa delta r' r beta := by
  rw [evenMajorant, evenMajorant]
  ring

theorem evenMajorant_periodic_row (kappa delta r' beta : ℝ) :
    Function.Periodic (fun r => evenMajorant kappa delta r r' beta) (2 * Real.pi) := by
  intro r
  show kappa * (delta + torusAbs (r + 2 * Real.pi) + torusAbs r' + torusAbs beta)
      = kappa * (delta + torusAbs r + torusAbs r' + torusAbs beta)
  rw [torusAbs_periodic r]

theorem evenMajorant_periodic_row' (kappa delta r beta : ℝ) :
    Function.Periodic (fun r' => evenMajorant kappa delta r r' beta) (2 * Real.pi) := by
  intro r'
  show kappa * (delta + torusAbs r + torusAbs (r' + 2 * Real.pi) + torusAbs beta)
      = kappa * (delta + torusAbs r + torusAbs r' + torusAbs beta)
  rw [torusAbs_periodic r']

theorem evenMajorant_periodic_col (kappa delta r r' : ℝ) :
    Function.Periodic (fun beta => evenMajorant kappa delta r r' beta) (2 * Real.pi) := by
  intro beta
  show kappa * (delta + torusAbs r + torusAbs r' + torusAbs (beta + 2 * Real.pi))
      = kappa * (delta + torusAbs r + torusAbs r' + torusAbs beta)
  rw [torusAbs_periodic beta]

theorem evenMajorant_measurable (kappa delta : ℝ) :
    Measurable fun z : ℝ × ℝ × ℝ => evenMajorant kappa delta z.1 z.2.1 z.2.2 := by
  unfold evenMajorant
  exact measurable_const.mul
    ((((measurable_const.add (torusAbs_measurable.comp measurable_fst)).add
      (torusAbs_measurable.comp (measurable_fst.comp measurable_snd))).add
      (torusAbs_measurable.comp (measurable_snd.comp measurable_snd))))

/-- `M ≥ κδ`: the lower bound behind the `L²` estimate for `K`. -/
theorem mul_le_evenMajorant {kappa : ℝ} (hkappa : 0 ≤ kappa) (delta r r' beta : ℝ) :
    kappa * delta ≤ evenMajorant kappa delta r r' beta := by
  rw [evenMajorant]
  have := torusAbs_nonneg r
  have := torusAbs_nonneg r'
  have := torusAbs_nonneg beta
  nlinarith

theorem evenMajorant_pos {kappa delta : ℝ} (hkappa : 0 < kappa) (hdelta : 0 < delta)
    (r r' beta : ℝ) : 0 < evenMajorant kappa delta r r' beta :=
  lt_of_lt_of_le (by positivity) (mul_le_evenMajorant hkappa.le delta r r' beta)

theorem evenMajorant_nonneg {kappa delta : ℝ} (hkappa : 0 ≤ kappa) (hdelta : 0 ≤ delta)
    (r r' beta : ℝ) : 0 ≤ evenMajorant kappa delta r r' beta :=
  le_trans (by positivity) (mul_le_evenMajorant hkappa delta r r' beta)

/-- `M` is bounded on the torus. -/
theorem evenMajorant_le {kappa delta : ℝ} (hkappa : 0 ≤ kappa) (r r' beta : ℝ) :
    evenMajorant kappa delta r r' beta ≤ kappa * (delta + 3 * Real.pi) := by
  rw [evenMajorant]
  have h1 := torusAbs_le_pi r
  have h2 := torusAbs_le_pi r'
  have h3 := torusAbs_le_pi beta
  nlinarith

/-! ## The majorization -/

/-- **The majorization.**  The multiplier `M(P)` of the manuscript's (35), at
the total frequency `P = (β, r+r'-p₂)` of the shifted row/column variables, is
dominated by the even majorant with `κ = 120`, as soon as `λ ≤ δ` and
`|p₂| ≤ δ`.

Both hypotheses hold in Version 4, where `δ = √λ + a` and `a = |p₁| ≥ |p₂|`:
then `λ = (√λ)² ≤ δ²`, so `λ ≤ δ` whenever `δ ≤ 1`, and `|p₂| ≤ a ≤ δ`.  No
hypothesis `λ ≤ a²` is needed, which is exactly what replacing `a` by `δ`
buys. -/
theorem multiplier_le_evenMajorant {q : Estimates.Parameters} {delta p₂ : ℝ}
    (hlam : q.lambda ≤ delta) (hp₂ : |p₂| ≤ delta) (r r' beta : ℝ) :
    Estimates.multiplier 40 q
        (Estimates.mixedTotalFrequency beta (r + r' - p₂))
      ≤ evenMajorant 120 delta r r' beta := by
  have hbeta : 2 * |Real.sin (beta / 2)| ≤ torusAbs beta :=
    two_abs_sin_half_le_torusAbs beta
  have halpha : 2 * |Real.sin ((r + r' - p₂) / 2)| ≤ torusAbs r + torusAbs r' + delta :=
    (two_abs_sin_half_mixedAlpha_le r r' p₂).trans (by linarith)
  have hdbeta := dispersion_le_two_abs_sin_half beta
  have hdalpha := dispersion_le_two_abs_sin_half (r + r' - p₂)
  have hr := torusAbs_nonneg r
  have hr' := torusAbs_nonneg r'
  have hb := torusAbs_nonneg beta
  simp only [Estimates.multiplier, Estimates.theta, Estimates.mixedTotalFrequency,
    evenMajorant, Matrix.cons_val_zero, Matrix.cons_val_one]
  linarith

/-- **The sharp pointwise majorant.**  The manuscript's `eq:M` takes
`M = 4(δ + |r| + |r'| + |β|)`.  The inequality in fact holds with `κ = 3`, and
with the multiplier at its own sharp normalization `κ = 1` rather than the `40`
that the projection-contraction chain carries.

Together with `symbolWeight_le_multiplier_one` this is the manuscript's
majorization at a constant better than the printed one.  It is stated
separately from `multiplier_le_evenMajorant` because the route to
`operatorEstimate` runs through frozen lemmas normalized at `κ = 40`; those
would have to be restated at a general `κ` before this sharp form could replace
the lossy one in the composed bound. -/
theorem multiplier_one_le_evenMajorant_three {q : Estimates.Parameters}
    {delta p₂ : ℝ} (hlam : q.lambda ≤ delta) (hp₂ : |p₂| ≤ delta) (r r' beta : ℝ) :
    Estimates.multiplier 1 q (Estimates.mixedTotalFrequency beta (r + r' - p₂))
      ≤ evenMajorant 3 delta r r' beta := by
  have hbeta : 2 * |Real.sin (beta / 2)| ≤ torusAbs beta :=
    two_abs_sin_half_le_torusAbs beta
  have halpha : 2 * |Real.sin ((r + r' - p₂) / 2)| ≤ torusAbs r + torusAbs r' + delta :=
    (two_abs_sin_half_mixedAlpha_le r r' p₂).trans (by linarith)
  have hdbeta := dispersion_le_two_abs_sin_half beta
  have hdalpha := dispersion_le_two_abs_sin_half (r + r' - p₂)
  have hr := torusAbs_nonneg r
  have hr' := torusAbs_nonneg r'
  have hb := torusAbs_nonneg beta
  simp only [Estimates.multiplier, Estimates.theta, Estimates.mixedTotalFrequency,
    evenMajorant, Matrix.cons_val_zero, Matrix.cons_val_one]
  linarith

/-! ## The integrated form -/

/-- The even-majorant energy `∫ M |k|²` of a raw type-`112` kernel, in the
`(β, r, r')` iteration order of `Manhattan.Glue.rawMultiplierEnergy`. -/
def evenMajorantEnergy (kappa delta : ℝ) (k : ℝ → ℝ → ℝ → ℂ) : ℝ :=
  Estimates.torusIntegral fun beta =>
    Estimates.torusIntegral fun r =>
      Estimates.torusIntegral fun r' =>
        evenMajorant kappa delta r r' beta * ‖k r r' beta‖ ^ 2

/-- Monotonicity of the iterated normalized torus integral, for bounded
measurable integrands. -/
theorem torusIntegral₃_mono {F G : ℝ → ℝ → ℝ → ℝ}
    (hF : Measurable fun z : ℝ × ℝ × ℝ => F z.1 z.2.1 z.2.2)
    (hG : Measurable fun z : ℝ × ℝ × ℝ => G z.1 z.2.1 z.2.2)
    {C : ℝ} (hFb : ∀ x y z, |F x y z| ≤ C) (hGb : ∀ x y z, |G x y z| ≤ C)
    (hle : ∀ x y z, F x y z ≤ G x y z) :
    (Estimates.torusIntegral fun x => Estimates.torusIntegral fun y =>
        Estimates.torusIntegral fun z => F x y z)
      ≤ Estimates.torusIntegral fun x => Estimates.torusIntegral fun y =>
          Estimates.torusIntegral fun z => G x y z := by
  have hinner : ∀ (H : ℝ → ℝ → ℝ → ℝ),
      (Measurable fun z : ℝ × ℝ × ℝ => H z.1 z.2.1 z.2.2) →
      (∀ x y z, |H x y z| ≤ C) →
      Integrable (fun x : ℝ => Estimates.torusIntegral fun y =>
          Estimates.torusIntegral fun z => H x y z)
        (volume.restrict Estimates.torus) := by
    intro H hH hHb
    refine Glue.integrable_torus_of_bound (C := C) ?_ ?_
    · have h1 : StronglyMeasurable fun w : (ℝ × ℝ) × ℝ => H w.1.1 w.1.2 w.2 :=
        (hH.comp ((measurable_fst.comp measurable_fst).prodMk
          ((measurable_snd.comp measurable_fst).prodMk measurable_snd))).stronglyMeasurable
      have h2 : StronglyMeasurable fun w : ℝ × ℝ =>
          Estimates.torusIntegral fun z => H w.1 w.2 z :=
        Glue.stronglyMeasurable_torusIntegral h1
      exact (Glue.stronglyMeasurable_torusIntegral h2).aestronglyMeasurable
    · intro x
      rw [Real.norm_eq_abs]
      exact Glue.abs_torusIntegral_le fun y =>
        Glue.abs_torusIntegral_le fun z => hHb x y z
  refine Glue.torusIntegral_mono (hinner F hF hFb) (hinner G hG hGb) fun x => ?_
  have hmidF : ∀ (H : ℝ → ℝ → ℝ → ℝ),
      (Measurable fun z : ℝ × ℝ × ℝ => H z.1 z.2.1 z.2.2) →
      (∀ x y z, |H x y z| ≤ C) →
      Integrable (fun y : ℝ => Estimates.torusIntegral fun z => H x y z)
        (volume.restrict Estimates.torus) := by
    intro H hH hHb
    refine Glue.integrable_torus_of_bound (C := C) ?_ ?_
    · have h1 : StronglyMeasurable fun w : ℝ × ℝ => H x w.1 w.2 :=
        (hH.comp (measurable_const.prodMk measurable_id)).stronglyMeasurable
      exact (Glue.stronglyMeasurable_torusIntegral h1).aestronglyMeasurable
    · intro y
      rw [Real.norm_eq_abs]
      exact Glue.abs_torusIntegral_le fun z => hHb x y z
  refine Glue.torusIntegral_mono (hmidF F hF hFb) (hmidF G hG hGb) fun y => ?_
  refine Glue.torusIntegral_mono ?_ ?_ fun z => hle x y z
  · refine Glue.integrable_torus_of_bound (C := C)
      ((hF.comp (measurable_const.prodMk
        (measurable_const.prodMk measurable_id))).aestronglyMeasurable) (fun z => ?_)
    rw [Real.norm_eq_abs]
    exact hFb x y z
  · refine Glue.integrable_torus_of_bound (C := C)
      ((hG.comp (measurable_const.prodMk
        (measurable_const.prodMk measurable_id))).aestronglyMeasurable) (fun z => ?_)
    rw [Real.norm_eq_abs]
    exact hGb x y z

/-- **The integrated majorization.**  The raw multiplier energy of the
manuscript is dominated by the even-majorant energy. -/
theorem rawMultiplierEnergy_le_evenMajorantEnergy {q : Estimates.Parameters}
    {delta p₂ : ℝ} {k : ℝ → ℝ → ℝ → ℂ}
    (hlam0 : 0 ≤ q.lambda) (hlam : q.lambda ≤ delta) (hp₂ : |p₂| ≤ delta)
    (hk : Glue.TorusBoundedThree k) :
    Glue.rawMultiplierEnergy 40 q p₂ k ≤ evenMajorantEnergy 120 delta k := by
  obtain ⟨hmeas, C, hC⟩ := hk
  have hCnonneg : 0 ≤ C := le_trans (norm_nonneg _) (hC 0 0 0)
  have hdelta : 0 ≤ delta := le_trans (abs_nonneg _) hp₂
  set B : ℝ := (40 * (q.lambda + 8) + 120 * (delta + 3 * Real.pi)) * C ^ 2 with hB
  have hnormsq : ∀ r r' beta : ℝ, ‖k r r' beta‖ ^ 2 ≤ C ^ 2 := by
    intro r r' beta
    exact pow_le_pow_left₀ (norm_nonneg _) (hC r r' beta) 2
  refine torusIntegral₃_mono (C := B) ?_ ?_ ?_ ?_ ?_
  · exact (Glue.measurable_multiplier_comp 40 q measurable_fst
      (((measurable_fst.comp measurable_snd).add
        (measurable_snd.comp measurable_snd)).sub measurable_const)).mul
      ((hmeas.comp ((measurable_fst.comp measurable_snd).prodMk
        ((measurable_snd.comp measurable_snd).prodMk measurable_fst))).norm.pow_const 2)
  · exact ((evenMajorant_measurable 120 delta).comp
      ((measurable_fst.comp measurable_snd).prodMk
        ((measurable_snd.comp measurable_snd).prodMk measurable_fst))).mul
      ((hmeas.comp ((measurable_fst.comp measurable_snd).prodMk
        ((measurable_snd.comp measurable_snd).prodMk measurable_fst))).norm.pow_const 2)
  · intro beta r r'
    have hm0 : 0 ≤ Estimates.multiplier 40 q
        (Estimates.mixedTotalFrequency beta (Glue.mixedAlpha p₂ r r')) :=
      Estimates.multiplier_nonneg (by norm_num) hlam0 _
    have hm : Estimates.multiplier 40 q
        (Estimates.mixedTotalFrequency beta (Glue.mixedAlpha p₂ r r'))
        ≤ 40 * (q.lambda + 8) := Glue.multiplier_le (by norm_num) _
    rw [abs_of_nonneg (mul_nonneg hm0 (sq_nonneg _)), hB]
    have hpi := Real.pi_pos
    nlinarith [hnormsq r r' beta, sq_nonneg (‖k r r' beta‖)]
  · intro beta r r'
    have hm0 : 0 ≤ evenMajorant 120 delta r r' beta :=
      evenMajorant_nonneg (by norm_num) hdelta r r' beta
    have hm : evenMajorant 120 delta r r' beta ≤ 120 * (delta + 3 * Real.pi) :=
      evenMajorant_le (by norm_num) r r' beta
    rw [abs_of_nonneg (mul_nonneg hm0 (sq_nonneg _)), hB]
    have hpi := Real.pi_pos
    nlinarith [hnormsq r r' beta, sq_nonneg (‖k r r' beta‖)]
  · intro beta r r'
    exact mul_le_mul_of_nonneg_right
      (multiplier_le_evenMajorant hlam hp₂ r r' beta) (sq_nonneg _)

end

end Manhattan.V4
