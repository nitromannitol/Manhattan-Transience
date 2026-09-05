import Manhattan.V4.Energy.Weight

/-!
# Version 4, Move 1: the `β` integral (6)

Ingredient (d) of Move 1 of the Version 4 argument: for `r` in
`Γ_δ = {√δ ≤ |r| ≤ 1/4}`, writing `ρ = |r|` and `L = log(1/ρ)`,

    `∫_𝕋 dm(β) / (B(r,β) + σ(r,β)) ≤ C / (ρ √L)`.

The proof splits the circle at the two thresholds `t₁ = ρ/√L` and `t₂ = √ρ`
(the note splits only at `√ρ`; the extra inner threshold replaces the arctangent
integral by the elementary `∫_a^b dx/x² ≤ 1/a`, so no special function is needed):

* `|β| ≤ t₁`: the constant bound `B + σ ≥ 2ρ²/π²` on an interval of length `2t₁`
  contributes `π²/(ρ√L)`;
* `t₁ ≤ |β| ≤ t₂`: the inner logarithmic bound `B + σ ≥ c β² L` contributes
  `(cL)⁻¹ · 1/t₁ = 1/(c ρ √L)` on each side;
* `t₂ ≤ |β| ≤ π`: the outer bound `B ≥ 2β²/π²` contributes `π²/(2√ρ)` on each
  side, and `π²/√ρ ≤ π²/(ρ√L)` because `ρ L ≤ 1` (`mul_log_inv_le_one`).

`t₁ ≤ t₂` holds because `t₁ ≤ ρ ≤ √ρ`, using `√L > 1` (`one_lt_log_inv`).

The main theorem is stated for an abstract positive weight `Φ` satisfying the
three pointwise lower bounds, plus one global positive lower bound `m` that
makes `Φ⁻¹` bounded and hence integrable. `betaIntegral_le` instantiates it at
`Φ(β) = λ + d(r) + d(β) + σ(β)`, which is the manuscript's `B + σ`; the only
input still owed by the parity construction is the inner lower bound on `σ`, isolated
here as the hypothesis `hSlow`.
-/

open MeasureTheory intervalIntegral

namespace Manhattan.V4.Energy

/-! ## Elementary integrability and tail integrals -/

/-- A bounded measurable real function is interval-integrable on every interval. -/
theorem intervalIntegrable_of_bounded {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ}
    (hb : ∀ x, |f x| ≤ C) (a b : ℝ) :
    IntervalIntegrable f volume a b := by
  refine ⟨?_, ?_⟩
  · haveI : IsFiniteMeasure (volume.restrict (Set.Ioc a b)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
    exact Integrable.mono' (integrable_const C) hf.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hb x)
  · haveI : IsFiniteMeasure (volume.restrict (Set.Ioc b a)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
    exact Integrable.mono' (integrable_const C) hf.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hb x)

/-- The normalized Haar integral on `𝕋` as an interval integral. -/
theorem torusIntegral_eq_intervalIntegral (f : ℝ → ℝ) :
    Manhattan.Estimates.torusIntegral f
      = (2 * Real.pi)⁻¹ * ∫ x in (-Real.pi)..Real.pi, f x := by
  rw [Manhattan.Estimates.torusIntegral, Manhattan.Estimates.torus, smul_eq_mul,
      intervalIntegral.integral_of_le]
  linarith [Real.pi_pos]

/-- `1/x²` is interval-integrable away from the origin. -/
theorem intervalIntegrable_inv_sq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun x : ℝ => (x ^ 2)⁻¹) volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.inv₀
  · exact continuousOn_pow 2
  · intro x hx
    rw [Set.mem_uIcc] at hx
    have hx_pos : 0 < x := by
      rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · linarith
      · linarith
    exact pow_ne_zero 2 (ne_of_gt hx_pos)

/-- `1/x²` is interval-integrable on the reflected interval. -/
theorem intervalIntegrable_inv_sq_neg {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun x : ℝ => (x ^ 2)⁻¹) volume (-b) (-a) := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.inv₀
  · exact continuousOn_pow 2
  · intro x hx
    rw [Set.mem_uIcc] at hx
    have hx_neg : x < 0 := by
      rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · linarith
      · linarith
    exact pow_ne_zero 2 (ne_of_lt hx_neg)

/-- The exact tail integral `∫_a^b dx/x² = 1/a - 1/b`. -/
theorem integral_inv_sq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ x in a..b, (x ^ 2)⁻¹) = 1 / a - 1 / b := by
  have h_int : IntervalIntegrable (fun x : ℝ => (x ^ 2)⁻¹) volume a b :=
    intervalIntegrable_inv_sq ha hab
  have h_deriv : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun y => -y⁻¹) ((x ^ 2)⁻¹) x := by
    intro x hx
    rw [Set.mem_uIcc] at hx
    have hx_ge : a ≤ x := by rcases hx with ⟨h1, _⟩ | ⟨h1, _⟩; exact h1; linarith
    have hx_pos : 0 < x := by linarith
    have h2 : HasDerivAt (fun y => -y⁻¹) (-(-(x ^ 2)⁻¹)) x := (hasDerivAt_inv hx_pos.ne').neg
    simp only [neg_neg] at h2
    exact h2
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h_deriv h_int]
  field_simp
  ring

/-- The tail bound used for the outer part of the `β` integral. -/
theorem integral_inv_sq_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ x in a..b, (x ^ 2)⁻¹) ≤ 1 / a := by
  rw [integral_inv_sq ha hab]
  have hbpos : 0 < b := lt_of_lt_of_le ha hab
  have hb_inv_nonneg : (0:ℝ) ≤ 1 / b := by positivity
  linarith

/-- The reflected tail bound. -/
theorem integral_inv_sq_neg_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ x in (-b)..(-a), (x ^ 2)⁻¹) ≤ 1 / a := by
  have comp_eq : (∫ x in a..b, ((-x) ^ 2)⁻¹) = ∫ x in (-b)..(-a), (x ^ 2)⁻¹ :=
    intervalIntegral.integral_comp_neg (fun x => (x ^ 2)⁻¹)
  simp only [neg_sq] at comp_eq
  rw [← comp_eq]
  exact integral_inv_sq_le ha hab

/-! ## The `β` integral (6) -/

set_option maxHeartbeats 1000000 in
theorem torusIntegral_inv_le
    {rho c m : ℝ} {Phi : ℝ → ℝ} (hmeas : Measurable Phi)
    (hc : 0 < c) (hrho : 0 < rho) (hrho' : rho ≤ 1 / 4)
    (hm : 0 < m) (hglob : ∀ b, m ≤ Phi b)
    (h1 : ∀ b, |b| ≤ Real.pi → 2 / Real.pi ^ 2 * rho ^ 2 ≤ Phi b)
    (h2 : ∀ b, |b| ≤ Real.sqrt rho → c * (b ^ 2 * Real.log (1 / rho)) ≤ Phi b)
    (h3 : ∀ b, |b| ≤ Real.pi → 2 / Real.pi ^ 2 * b ^ 2 ≤ Phi b) :
    Manhattan.Estimates.torusIntegral (fun b => (Phi b)⁻¹)
      ≤ (Real.pi ^ 2 + 1 / c) / (rho * Real.sqrt (Real.log (1 / rho))) := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hpi2' : (2:ℝ) ≤ Real.pi := Real.two_le_pi
  have hpi2 : (0:ℝ) < Real.pi ^ 2 := by positivity
  have hL1 : 1 < Real.log (1 / rho) := one_lt_log_inv hrho hrho'
  have hL0 : (0:ℝ) < Real.log (1 / rho) := by linarith
  have hL2 : rho * Real.log (1 / rho) ≤ 1 := mul_log_inv_le_one hrho hrho'
  set S : ℝ := Real.sqrt (Real.log (1 / rho)) with hSdef
  have hS0 : 0 < S := Real.sqrt_pos.mpr hL0
  have hSsq : S ^ 2 = Real.log (1 / rho) := Real.sq_sqrt hL0.le
  have hS1 : 1 < S := by nlinarith
  set t2 : ℝ := Real.sqrt rho with ht2
  have ht2pos : 0 < t2 := Real.sqrt_pos.mpr hrho
  have ht2sq : t2 * t2 = rho := Real.mul_self_sqrt hrho.le
  have ht2half : t2 ≤ 1 / 2 := sqrt_le_half hrho'
  have hrt2 : rho ≤ t2 := le_sqrt_self hrho.le (by linarith)
  clear_value S t2
  set t1 : ℝ := rho / S with ht1
  have ht1pos : 0 < t1 := div_pos hrho hS0
  have ht1le : t1 ≤ rho := by rw [ht1, div_le_iff₀ hS0]; nlinarith
  have ht12 : t1 ≤ t2 := le_trans ht1le hrt2
  have ht2pi : t2 ≤ Real.pi := by linarith
  clear_value t1
  -- `t2 S ≤ 1`, hence `ρ S ≤ t2`: this absorbs the outer piece into the main term.
  have ht2S : t2 * S ≤ 1 := by nlinarith [mul_pos ht2pos hS0]
  have hrhoS : rho * S ≤ t2 := by nlinarith
  have hq0 : (0:ℝ) < 2 / Real.pi ^ 2 * rho ^ 2 := by positivity
  have hPhipos : ∀ b, 0 < Phi b := fun b => lt_of_lt_of_le hm (hglob b)
  set F : ℝ → ℝ := fun b => (Phi b)⁻¹ with hF
  have hFpos : ∀ b, 0 < F b := fun b => inv_pos.mpr (hPhipos b)
  have hKdef : (2 / Real.pi ^ 2 * rho ^ 2)⁻¹ = Real.pi ^ 2 / (2 * rho ^ 2) := by
    field_simp
  have hFub : ∀ b, |b| ≤ Real.pi → F b ≤ Real.pi ^ 2 / (2 * rho ^ 2) := by
    intro b hb
    have h := inv_anti₀ hq0 (h1 b hb)
    rw [hKdef] at h
    exact h
  have hFabs : ∀ b, |F b| ≤ m⁻¹ := by
    intro b
    rw [abs_of_pos (hFpos b)]
    exact inv_anti₀ hm (hglob b)
  have hFmeas : Measurable F := hmeas.inv
  have hFii : ∀ a b : ℝ, IntervalIntegrable F volume a b :=
    fun a b => intervalIntegrable_of_bounded hFmeas hFabs a b
  have hFapp : ∀ x, F x = (Phi x)⁻¹ := fun x => by rw [hF]
  clear_value F
  -- the five-way split of the torus into the two logarithmic zones and the outer zone
  have e1 := intervalIntegral.integral_add_adjacent_intervals
    (hFii (-Real.pi) (-t2)) (hFii (-t2) (-t1))
  have e2 := intervalIntegral.integral_add_adjacent_intervals
    (hFii (-Real.pi) (-t1)) (hFii (-t1) t1)
  have e3 := intervalIntegral.integral_add_adjacent_intervals
    (hFii (-Real.pi) t1) (hFii t1 t2)
  have e4 := intervalIntegral.integral_add_adjacent_intervals
    (hFii (-Real.pi) t2) (hFii t2 Real.pi)
  -- middle piece: the constant bound `Φ ≥ 2ρ²/π²`
  have b3 : (∫ x in (-t1)..t1, F x) ≤ 2 * t1 * (Real.pi ^ 2 / (2 * rho ^ 2)) := by
    have hle : -t1 ≤ t1 := by linarith
    have h := intervalIntegral.integral_mono_on hle (hFii (-t1) t1)
      _root_.intervalIntegrable_const (fun x hx => hFub x (by
        rw [abs_le]
        constructor
        · linarith [hx.1]
        · linarith [hx.2]))
    rw [intervalIntegral.integral_const, smul_eq_mul] at h
    calc (∫ x in (-t1)..t1, F x) ≤ (t1 - -t1) * (Real.pi ^ 2 / (2 * rho ^ 2)) := h
      _ = 2 * t1 * (Real.pi ^ 2 / (2 * rho ^ 2)) := by ring
  have hcoef : (0:ℝ) ≤ 1 / (c * Real.log (1 / rho)) := by positivity
  have hlogpt : ∀ x : ℝ, x ≠ 0 → |x| ≤ t2 →
      F x ≤ (1 / (c * Real.log (1 / rho))) * (x ^ 2)⁻¹ := by
    intro x hxne habs
    rw [hFapp x]
    have hden : 0 < c * (x ^ 2 * Real.log (1 / rho)) := by positivity
    have hlow := inv_anti₀ hden (h2 x habs)
    have heq : (c * (x ^ 2 * Real.log (1 / rho)))⁻¹
        = (1 / (c * Real.log (1 / rho))) * (x ^ 2)⁻¹ := by
      field_simp
    rw [heq] at hlow
    exact hlow
  have b4 : (∫ x in t1..t2, F x) ≤ (1 / (c * Real.log (1 / rho))) * (1 / t1) := by
    have hpt : ∀ x ∈ Set.Icc t1 t2,
        F x ≤ (1 / (c * Real.log (1 / rho))) * (x ^ 2)⁻¹ := by
      intro x hx
      have hxpos : 0 < x := lt_of_lt_of_le ht1pos hx.1
      exact hlogpt x (ne_of_gt hxpos) (by rw [abs_of_pos hxpos]; exact hx.2)
    have hg : IntervalIntegrable
        (fun x : ℝ => (1 / (c * Real.log (1 / rho))) * (x ^ 2)⁻¹) volume t1 t2 :=
      (intervalIntegrable_inv_sq ht1pos ht12).const_mul _
    have hmono := intervalIntegral.integral_mono_on ht12 (hFii t1 t2) hg hpt
    rw [intervalIntegral.integral_const_mul] at hmono
    exact hmono.trans (mul_le_mul_of_nonneg_left (integral_inv_sq_le ht1pos ht12) hcoef)
  have b2 : (∫ x in (-t2)..(-t1), F x) ≤ (1 / (c * Real.log (1 / rho))) * (1 / t1) := by
    have hle : -t2 ≤ -t1 := by linarith
    have hpt : ∀ x ∈ Set.Icc (-t2) (-t1),
        F x ≤ (1 / (c * Real.log (1 / rho))) * (x ^ 2)⁻¹ := by
      intro x hx
      have hxneg : x < 0 := lt_of_le_of_lt hx.2 (by linarith)
      exact hlogpt x (ne_of_lt hxneg) (by rw [abs_of_neg hxneg]; linarith [hx.1])
    have hg : IntervalIntegrable
        (fun x : ℝ => (1 / (c * Real.log (1 / rho))) * (x ^ 2)⁻¹) volume (-t2) (-t1) :=
      (intervalIntegrable_inv_sq_neg ht1pos ht12).const_mul _
    have hmono := intervalIntegral.integral_mono_on hle (hFii (-t2) (-t1)) hg hpt
    rw [intervalIntegral.integral_const_mul] at hmono
    exact hmono.trans (mul_le_mul_of_nonneg_left (integral_inv_sq_neg_le ht1pos ht12) hcoef)
  -- outer pieces: the quadratic bound `Φ ≥ 2β²/π²`
  have hcoef2 : (0:ℝ) ≤ Real.pi ^ 2 / 2 := by positivity
  have houtpt : ∀ x : ℝ, x ≠ 0 → |x| ≤ Real.pi →
      F x ≤ (Real.pi ^ 2 / 2) * (x ^ 2)⁻¹ := by
    intro x hxne hxpi
    rw [hFapp x]
    have hden : 0 < 2 / Real.pi ^ 2 * x ^ 2 := by positivity
    have hlow := inv_anti₀ hden (h3 x hxpi)
    have heq : (2 / Real.pi ^ 2 * x ^ 2)⁻¹ = (Real.pi ^ 2 / 2) * (x ^ 2)⁻¹ := by
      field_simp
    rw [heq] at hlow
    exact hlow
  have b5 : (∫ x in t2..Real.pi, F x) ≤ (Real.pi ^ 2 / 2) * (1 / t2) := by
    have hpt : ∀ x ∈ Set.Icc t2 Real.pi, F x ≤ (Real.pi ^ 2 / 2) * (x ^ 2)⁻¹ := by
      intro x hx
      exact houtpt x (ne_of_gt (lt_of_lt_of_le ht2pos hx.1))
        (by rw [abs_of_pos (lt_of_lt_of_le ht2pos hx.1)]; exact hx.2)
    have hg : IntervalIntegrable
        (fun x : ℝ => (Real.pi ^ 2 / 2) * (x ^ 2)⁻¹) volume t2 Real.pi :=
      (intervalIntegrable_inv_sq ht2pos ht2pi).const_mul _
    have hmono := intervalIntegral.integral_mono_on ht2pi (hFii t2 Real.pi) hg hpt
    rw [intervalIntegral.integral_const_mul] at hmono
    exact hmono.trans (mul_le_mul_of_nonneg_left (integral_inv_sq_le ht2pos ht2pi) hcoef2)
  have b1 : (∫ x in (-Real.pi)..(-t2), F x) ≤ (Real.pi ^ 2 / 2) * (1 / t2) := by
    have hle : -Real.pi ≤ -t2 := by linarith
    have hpt : ∀ x ∈ Set.Icc (-Real.pi) (-t2), F x ≤ (Real.pi ^ 2 / 2) * (x ^ 2)⁻¹ := by
      intro x hx
      exact houtpt x (ne_of_lt (lt_of_le_of_lt hx.2 (by linarith)))
        (by rw [abs_of_neg (lt_of_le_of_lt hx.2 (by linarith))]; linarith [hx.1])
    have hg : IntervalIntegrable
        (fun x : ℝ => (Real.pi ^ 2 / 2) * (x ^ 2)⁻¹) volume (-Real.pi) (-t2) :=
      (intervalIntegrable_inv_sq_neg ht2pos ht2pi).const_mul _
    have hmono := intervalIntegral.integral_mono_on hle (hFii (-Real.pi) (-t2)) hg hpt
    rw [intervalIntegral.integral_const_mul] at hmono
    exact hmono.trans (mul_le_mul_of_nonneg_left (integral_inv_sq_neg_le ht2pos ht2pi) hcoef2)
  have hT : (0:ℝ) < rho * S := by positivity
  have c3 : 2 * t1 * (Real.pi ^ 2 / (2 * rho ^ 2)) = Real.pi ^ 2 / (rho * S) := by
    rw [ht1]; field_simp
  have c4 : (1 / (c * Real.log (1 / rho))) * (1 / t1) = 1 / (c * (rho * S)) := by
    rw [ht1, ← hSsq]; field_simp
  have c5 : (Real.pi ^ 2 / 2) * (1 / t2) ≤ Real.pi ^ 2 / (2 * (rho * S)) := by
    rw [mul_one_div, div_div]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)
  have hb3 : (∫ x in (-t1)..t1, F x) ≤ Real.pi ^ 2 / (rho * S) := by rw [← c3]; exact b3
  have hb4 : (∫ x in t1..t2, F x) ≤ 1 / (c * (rho * S)) := by rw [← c4]; exact b4
  have hb2 : (∫ x in (-t2)..(-t1), F x) ≤ 1 / (c * (rho * S)) := by rw [← c4]; exact b2
  have hb5 : (∫ x in t2..Real.pi, F x) ≤ Real.pi ^ 2 / (2 * (rho * S)) := le_trans b5 c5
  have hb1 : (∫ x in (-Real.pi)..(-t2), F x) ≤ Real.pi ^ 2 / (2 * (rho * S)) := le_trans b1 c5
  have hAsum : (∫ x in (-Real.pi)..Real.pi, F x)
      ≤ 2 * (Real.pi ^ 2 / (2 * (rho * S)))
        + 2 * (1 / (c * (rho * S)))
        + Real.pi ^ 2 / (rho * S) := by
    linarith [e1, e2, e3, e4, hb1, hb2, hb3, hb4, hb5]
  have hAsum' : (∫ x in (-Real.pi)..Real.pi, F x)
      ≤ (2 * Real.pi ^ 2 + 2 / c) / (rho * S) := by
    have hsplit : (2 * Real.pi ^ 2 + 2 / c) / (rho * S)
        = 2 * (Real.pi ^ 2 / (2 * (rho * S))) + 2 * (1 / (c * (rho * S)))
          + Real.pi ^ 2 / (rho * S) := by
      field_simp; ring
    rw [hsplit]
    exact hAsum
  rw [torusIntegral_eq_intervalIntegral]
  have heq : (2 * Real.pi)⁻¹ * ((2 * Real.pi ^ 2 + 2 / c) / (rho * S))
      = (Real.pi ^ 2 + 1 / c) / (Real.pi * (rho * S)) := by
    field_simp
  have hnum : (0:ℝ) ≤ Real.pi ^ 2 + 1 / c := by positivity
  have hden : rho * S ≤ Real.pi * (rho * S) := by nlinarith
  calc (2 * Real.pi)⁻¹ * ∫ x in (-Real.pi)..Real.pi, F x
      ≤ (2 * Real.pi)⁻¹ * ((2 * Real.pi ^ 2 + 2 / c) / (rho * S)) :=
        mul_le_mul_of_nonneg_left hAsum' (by positivity)
    _ = (Real.pi ^ 2 + 1 / c) / (Real.pi * (rho * S)) := heq
    _ ≤ (Real.pi ^ 2 + 1 / c) / (rho * S) := div_le_div_of_nonneg_left hnum hT hden

/-! ## The inner lower bound on `σ`, and the manuscript's form of (6) -/

/-- **The inner-zone lower bound on the logarithmic correction `σ`.** With
`σ(r,β) = sin²β · J` and `J ≥ (κπ)⁻¹ log(1 + π/(δ + ρ + |β|))` (which is the
value of the fibre integral `∫ dm(r')/M(r,r',β)` for the even majorant
`M = κ(δ + |r| + |r'| + |β|)`), the hypotheses `δ ≤ ρ²`, `ρ ≤ 1/4`, `|β| ≤ √ρ`
give `δ + ρ + |β| ≤ 2√ρ`, hence `log(1 + π/(δ+ρ+|β|)) ≥ log(1/√ρ) = ½ log(1/ρ)`;
Jordan's inequality `sin²β ≥ (4/π²)β²` then gives the constant `c = 2/(π³κ)`.
This is the sole input the `β` integral needs from the parity construction. -/
theorem sigma_inner_lower {kappa delta rho beta J : ℝ}
    (hkappa : 0 < kappa) (hdelta : 0 ≤ delta) (hdrho : delta ≤ rho ^ 2)
    (hrho : 0 < rho) (hrho' : rho ≤ 1 / 4)
    (hb : |beta| ≤ Real.sqrt rho)
    (hJ : (kappa * Real.pi)⁻¹ * Real.log (1 + Real.pi / (delta + rho + |beta|)) ≤ J) :
    2 / (Real.pi ^ 3 * kappa) * (beta ^ 2 * Real.log (1 / rho))
      ≤ Real.sin beta ^ 2 * J := by
  set u := Real.sqrt rho with hu_def
  set L := Real.log (1 / rho) with hL_def
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpi2 : (2 : ℝ) ≤ Real.pi := Real.two_le_pi
  have hu : 0 < u := Real.sqrt_pos.mpr hrho
  have huu : u * u = rho := Real.mul_self_sqrt hrho.le
  have huh : u ≤ 1 / 2 := sqrt_le_half hrho'
  have hsum : delta + rho + |beta| ≤ 2 * u := by
    nlinarith [huu, huh, hu, hb, hdrho, hdelta]
  have hsumpos : 0 < delta + rho + |beta| := by linarith [abs_nonneg beta]
  have h5a : Real.pi / (2 * u) ≤ Real.pi / (delta + rho + |beta|) := by
    rw [div_le_div_iff₀ (by positivity) hsumpos]
    nlinarith [hpi]
  have h5b : 1 / u ≤ Real.pi / (2 * u) := by
    have h2u_pos : 0 < 2 * u := by positivity
    have h5b_calc : (2 : ℝ) / (2 * u) ≤ Real.pi / (2 * u) := by
      rw [div_le_div_iff₀ h2u_pos h2u_pos]
      nlinarith [hpi2]
    calc 1 / u = 2 / (2 * u) := by ring
      _ ≤ Real.pi / (2 * u) := h5b_calc
  have hfrac : 1 / u ≤ 1 + Real.pi / (delta + rho + |beta|) := by linarith [h5a, h5b]
  have hloglow : Real.log (1 / u) ≤ Real.log (1 + Real.pi / (delta + rho + |beta|)) :=
    Real.log_le_log (by positivity) hfrac
  have hhalf : Real.log (1 / u) = (1 / 2) * Real.log (1 / rho) := by
    rw [show u = Real.sqrt rho from hu_def]
    have eq1 : Real.log (1 / Real.sqrt rho) = -Real.log (Real.sqrt rho) := by
      rw [Real.log_div (by norm_num) (Real.sqrt_pos.mpr hrho).ne']
      simp
    have eq2 : Real.log (Real.sqrt rho) = Real.log rho / 2 := Real.log_sqrt hrho.le
    have eq3 : Real.log (1 / rho) = -Real.log rho := by
      rw [Real.log_div (by norm_num) hrho.ne']
      simp
    rw [eq1, eq2, eq3]
    ring
  have hL_pos : 0 < Real.log (1 / rho) := log_inv_pos hrho hrho'
  have hJlow : (kappa * Real.pi)⁻¹ * ((1 / 2) * Real.log (1 / rho)) ≤ J := by
    have step1 : (kappa * Real.pi)⁻¹ * Real.log (1 / u) ≤ J :=
      le_trans (mul_le_mul_of_nonneg_left hloglow (by positivity)) hJ
    rw [hhalf] at step1
    exact step1
  have hsin : 4 / Real.pi ^ 2 * beta ^ 2 ≤ Real.sin beta ^ 2 := by
    have hbeta_bound : |beta| ≤ Real.pi / 2 := by
      calc |beta| ≤ u := hb
        _ ≤ 1 / 2 := huh
        _ ≤ Real.pi / 2 := by linarith [hpi2]
    exact sq_le_sin_sq hbeta_bound
  have key : (4 / Real.pi ^ 2 * beta ^ 2) *
      ((kappa * Real.pi)⁻¹ * ((1 / 2) * Real.log (1 / rho)))
      = 2 / (Real.pi ^ 3 * kappa) * (beta ^ 2 * Real.log (1 / rho)) := by ring
  have goal_eq : 2 / (Real.pi ^ 3 * kappa) * (beta ^ 2 * L)
      = 2 / (Real.pi ^ 3 * kappa) * (beta ^ 2 * Real.log (1 / rho)) := by rw [hL_def]
  rw [goal_eq, ← key]
  exact mul_le_mul hsin hJlow (by positivity) (by positivity)

/-- **Ingredient (d) of Move 1, in the manuscript's variables.** With
`B(r,β) = λ + d(r) + d(β)` and an abstract nonnegative `σ` obeying the inner
lower bound `hSlow`, the `β` integral of `(B + σ)⁻¹` obeys `(6)`:

    `∫ dm(β)/(B + σ) ≤ (π² + 1/c) / (|r| √(log(1/|r|)))`.

The hypothesis `hSlow` is exactly what `sigma_inner_lower` supplies, with
`c = 2/(π³κ)`. -/
theorem betaIntegral_le {lambda c r : ℝ} {Sig : ℝ → ℝ}
    (hmeasSig : Measurable Sig) (hSig : ∀ b, 0 ≤ Sig b)
    (hlam : 0 < lambda) (hc : 0 < c)
    (hr : 0 < |r|) (hr1 : |r| ≤ 1 / 4)
    (hSlow : ∀ b, |b| ≤ Real.sqrt |r| → c * (b ^ 2 * Real.log (1 / |r|)) ≤ Sig b) :
    Manhattan.Estimates.torusIntegral (fun b =>
        (lambda + Manhattan.Estimates.dispersion r + Manhattan.Estimates.dispersion b
          + Sig b)⁻¹)
      ≤ (Real.pi ^ 2 + 1 / c) / (|r| * Real.sqrt (Real.log (1 / |r|))) := by
  have hpi2 : (2:ℝ) ≤ Real.pi := Real.two_le_pi
  have hrpi : |r| ≤ Real.pi := by linarith
  have hdr : 0 ≤ Manhattan.Estimates.dispersion r := Manhattan.Estimates.dispersion_nonneg r
  have hmeasD : Measurable (fun b : ℝ => Manhattan.Estimates.dispersion b) := by
    unfold Manhattan.Estimates.dispersion
    exact measurable_const.sub Real.continuous_cos.measurable
  refine torusIntegral_inv_le
    ((measurable_const.add hmeasD).add hmeasSig) hc hr hr1 hlam ?_ ?_ ?_ ?_
  · intro b
    have := Manhattan.Estimates.dispersion_nonneg b
    have := hSig b
    linarith
  · intro b _
    have hdb := Manhattan.Estimates.dispersion_nonneg b
    have hsb := hSig b
    have hq : 2 / Real.pi ^ 2 * |r| ^ 2 ≤ Manhattan.Estimates.dispersion r := by
      have h := two_sq_div_pi_sq_le_dispersion hrpi
      have heq : 2 * r ^ 2 / Real.pi ^ 2 = 2 / Real.pi ^ 2 * r ^ 2 := by ring
      rw [sq_abs]
      linarith
    linarith
  · intro b hb
    have hdb := Manhattan.Estimates.dispersion_nonneg b
    have := hSlow b hb
    linarith
  · intro b hb
    have h := two_sq_div_pi_sq_le_dispersion hb
    have heq : 2 * b ^ 2 / Real.pi ^ 2 = 2 / Real.pi ^ 2 * b ^ 2 := by ring
    have hsb := hSig b
    linarith

end Manhattan.V4.Energy
