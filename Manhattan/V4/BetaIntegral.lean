/-
Ingredients for the column-frequency integral of the manuscript's `eq:beta`.

The manuscript splits that integral at `|β| = √ρ`, bounds the weight below by a
quadratic on the inner interval and by `2β²/π²` outside, and evaluates the two
pieces.  This file collects the two evaluations.  They are Mathlib-only and
independent of the Manhattan model.

Each is verified against
the stated form before landing.
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

namespace Manhattan.V4.Beta

open MeasureTheory Set Filter Topology

theorem integral_Ioi_inv_sq {c : ℝ} (hc : 0 < c) :
    (∫ x in Ioi c, (x ^ 2)⁻¹) = c⁻¹ := by
  have hderiv : ∀ x ∈ Ioi c, HasDerivAt (fun x : ℝ => -x⁻¹) ((x ^ 2)⁻¹) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (hc.trans hx)
    simpa using (hasDerivAt_inv hx0).fun_neg
  have hcont : ContinuousWithinAt (fun x : ℝ => -x⁻¹) (Ici c) c :=
    ((hasDerivAt_inv (x := c) (ne_of_gt hc)).fun_neg).continuousAt.continuousWithinAt
  exact (integral_Ioi_of_hasDerivAt_of_nonneg hcont hderiv
    (fun x _ => inv_nonneg.2 (sq_nonneg x))
    (Filter.Tendsto.neg tendsto_inv_atTop_zero)).trans (by simp)

/-! ### The inner piece of `eq:beta`

On `|β| ≤ √ρ` the manuscript bounds the weight below by `2ρ²/π² + β² log(1/ρ)/(2π³)`
and integrates the reciprocal quadratic over the whole line.  Halving that gives
the half_line_inv_add_mul_sq-line evaluation below, `π/(2√(ab))`. -/

theorem integral_Ioi_inv_add_mul_sq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ x in Ioi (0:ℝ), (a + b * x ^ 2)⁻¹) = Real.pi / (2 * Real.sqrt (a * b)) := by
  set c := √(b / a) with hc_def
  have hc : 0 < c := Real.sqrt_pos.mpr (by positivity)
  have hac : a * c = √(a * b) := by
    calc a * c = a * (√b / √a) := by rw [hc_def, Real.sqrt_div' b ha.le]
      _ = √a * √b := by field_simp; rw [Real.sq_sqrt ha.le]
      _ = √(a * b) := by rw [Real.sqrt_mul ha.le b]
  have hfun : ∀ x : ℝ, (a + b * x ^ 2)⁻¹ = a⁻¹ * (1 + (c * x) ^ 2)⁻¹ := by
    intro x
    rw [hc_def, mul_pow, Real.sq_sqrt (le_of_lt (div_pos hb ha))]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi (fun x _ => hfun x)]
  rw [integral_const_mul _ _, integral_comp_mul_left_Ioi
    (fun u : ℝ => (1 + u ^ 2)⁻¹) 0 hc]
  simp only [smul_eq_mul, mul_zero]
  rw [integral_Ioi_inv_one_add_sq, ← hac]
  field_simp
  simp

/-! ### The radial integral of the frequency bound

`∫₀^R x/(λ+x²) dx = ½ log((λ+R²)/λ)`, the exact evaluation the three-region
frequency integration needs where the assembled route bounds the integrand at
its maximum instead. -/

theorem integral_Ioo_x_div_add_sq {lam R : ℝ} (hlam : 0 < lam) (hR : 0 < R) :
    (∫ x in Ioo (0:ℝ) R, x / (lam + x ^ 2))
      = Real.log ((lam + R ^ 2) / lam) / 2 := by
  have hder : ∀ x : ℝ, HasDerivAt
      (fun y : ℝ => Real.log (lam + y ^ 2) / 2) (x / (lam + x ^ 2)) x := by
    intro x
    have hpos : 0 < lam + x ^ 2 := by nlinarith [hlam]
    have hinner : HasDerivAt (fun y : ℝ => lam + y ^ 2) (2 * x) x :=
      ((hasDerivAt_pow 2 x).const_add lam).congr_deriv (by simp)
    have hlog := (Real.hasDerivAt_log (ne_of_gt hpos)).comp x hinner
    refine (hlog.div_const 2).congr_deriv ?_
    field_simp
  have hcont : Continuous (fun x : ℝ => x / (lam + x ^ 2)) := by
    exact Continuous.div continuous_id
      (by continuity) (fun x => by nlinarith [hlam])
  have hint : IntervalIntegrable (fun x : ℝ => x / (lam + x ^ 2)) volume 0 R :=
    hcont.intervalIntegrable 0 R
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hder x) hint
  have hval : Real.log ((lam + R ^ 2) / lam) / 2
      = Real.log (lam + R ^ 2) / 2 - Real.log (lam + 0 ^ 2) / 2 := by
    rw [Real.log_div (by nlinarith [hR]) hlam.ne.symm]
    have h0 : Real.log (lam + 0 ^ 2) = Real.log lam := by
      congr 1
      ring
    rw [h0]
    ring
  rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo]
  rw [← intervalIntegral.integral_of_le hR.le]
  exact hftc.trans hval.symm

/-! ### The two evaluations combined

With the manuscript's inner coefficients `A = 2ρ²/π²` and
`B = log(1/ρ)/(2π³)`, the geometric mean is `√(AB) = ρ√(log(1/ρ))/π^{5/2}`, so
the half_line_inv_add_mul_sq-line evaluation `π/(2√(AB))` is exactly `π^{7/2}/(2ρ√(log(1/ρ)))`.
Normalizing by `1/(2π)` and doubling for the two sides of the origin turns that
into the manuscript's `π^{5/2}/(2ρ√(log(1/ρ)))`. -/

theorem sqrt_inner_coefficients {rho : ℝ} (hrho : 0 < rho) (hlog : 0 < Real.log (1 / rho)) :
    Real.sqrt (2 * rho ^ 2 / Real.pi ^ 2 * (Real.log (1 / rho) / (2 * Real.pi ^ 3)))
      = rho * Real.sqrt (Real.log (1 / rho)) / Real.pi ^ (5/2 : ℝ) := by
  have hpi := Real.pi_pos
  have hprod : 2 * rho ^ 2 / Real.pi ^ 2 * (Real.log (1 / rho) / (2 * Real.pi ^ 3))
      = rho ^ 2 * Real.log (1 / rho) / Real.pi ^ 5 := by
    field_simp
  rw [hprod]
  have h5 : Real.pi ^ (5/2 : ℝ) = Real.sqrt (Real.pi ^ 5) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast Real.pi 5, ← Real.rpow_mul hpi.le]
    norm_num
  rw [h5, Real.sqrt_div' _ (by positivity), Real.sqrt_mul (by positivity),
    Real.sqrt_sq hrho.le]

/-! ### Convergence of the frequency integral

The substitution `u = log(1/x)` turns the frequency integrand into `(1+u)^{-3/2}`,
which converges.  This is the finiteness the manuscript's frequency integration
uses at the end of `prop:frequency`. -/

theorem integrableOn_inv_mul_logPow {r0 : ℝ} (hr0 : 0 < r0) (hr1 : r0 < 1) :
    IntegrableOn (fun x : ℝ => (x * (1 + Real.log (1 / x)) ^ (3/2 : ℝ))⁻¹)
      (Ioo 0 r0) := by
  have hr01 : 0 < 1 / r0 := by positivity
  have hone : 1 < 1 / r0 := (one_lt_div hr0).mpr hr1
  have hapos : 0 < Real.log (1 / r0) := Real.log_pos hone
  let a := Real.log (1 / r0)
  have hlog : a = -(Real.log r0) := by
    show Real.log (1 / r0) = -(Real.log r0)
    rw [one_div r0, Real.log_inv]
  have hclean : IntegrableOn (fun u : ℝ => (1 + u) ^ (-(3/2 : ℝ))) (Ioi a) := by
    refine (integrableOn_add_rpow_Ioi_of_lt (a := -(3/2 : ℝ)) (m := 1) (c := a)
      (by norm_num) (by linarith)).congr_fun
      (fun u _ => by rw [add_comm]) measurableSet_Ioi
  have himg : (fun u : ℝ => Real.exp (-u)) '' Ioi a = Ioo 0 r0 := by
    ext x
    simp only [mem_image, mem_Ioo, mem_Ioi]
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨Real.exp_pos _, ?_⟩
      have hlt : -u < Real.log r0 := by linarith [hlog, hu]
      exact (Real.lt_log_iff_exp_lt hr0).mp hlt
    · rintro ⟨hx0, hx1⟩
      have hxlog : Real.log x < Real.log r0 := (Real.log_lt_log_iff hx0 hr0).mpr hx1
      refine ⟨-Real.log x, ?_, ?_⟩
      · linarith
      · rw [neg_neg]
        exact Real.exp_log hx0
  rw [← himg]
  refine (integrableOn_image_iff_integrableOn_abs_deriv_smul
    (f := fun u : ℝ => Real.exp (-u)) (f' := fun u : ℝ => -Real.exp (-u))
    (g := fun x : ℝ => (x * (1 + Real.log (1 / x)) ^ (3/2 : ℝ))⁻¹)
    measurableSet_Ioi ?_ ?_).mpr ?_
  · intro u _
    refine (((Real.hasDerivAt_exp (-u)).comp u (hasDerivAt_neg u)).hasDerivWithinAt).congr_deriv ?_
    simp
  · intro u _ v _ huv
    exact neg_injective (Real.exp_injective huv)
  · have hfun : EqOn (fun u : ℝ => (1 + u) ^ (-(3/2 : ℝ)))
        (fun u : ℝ => |(-Real.exp (-u))| •
          (fun x : ℝ => (x * (1 + Real.log (1 / x)) ^ (3/2 : ℝ))⁻¹)
            (Real.exp (-u))) (Ioi a) := by
      intro u hu
      simp only [abs_neg, smul_eq_mul]
      rw [abs_of_pos (Real.exp_pos (-u)), one_div (Real.exp (-u)), Real.log_inv, Real.log_exp]
      simp only [Real.exp_neg, div_eq_inv_mul]
      field_simp
      have hpos : (0 : ℝ) ≤ 1 + u := by linarith [mem_Ioi.mp hu]
      rw [Real.rpow_neg hpos, inv_eq_one_div]
    exact hclean.congr_fun hfun measurableSet_Ioi

/-! ### The manuscript's two closing inequalities

`eq:beta` finishes by absorbing the tail with `ρ log(1/ρ) ≤ 1` and collecting
the constant as `(π^{5/2} + π)/2 < 11`. -/

theorem pi_rpow_five_halves_add_pi_lt :
    (Real.pi ^ (5 / 2 : ℝ) + Real.pi) / 2 < 11 := by
  have hpi : Real.pi < 63 / 20 := by linarith [Real.pi_lt_d2]
  have hsq : Real.pi ^ 2 < 3969 / 400 := by
    have hmono := Real.rpow_lt_rpow Real.pi_pos.le hpi (show (0 : ℝ) < 2 by norm_num)
    norm_num at hmono
    exact hmono
  have hpi' : Real.pi < 81 / 25 := by linarith [hpi]
  have hsqrt : Real.sqrt Real.pi < 9 / 5 := by
    have hmono := Real.sqrt_lt_sqrt Real.pi_pos.le hpi'
    have h95 : Real.sqrt (81 / 25 : ℝ) = 9 / 5 := by
      rw [show (81 / 25 : ℝ) = (9 / 5) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rwa [h95] at hmono
  have hid : Real.pi ^ (5 / 2 : ℝ) = Real.pi ^ 2 * Real.sqrt Real.pi := by
    rw [show ((5 : ℝ) / 2) = 2 + 1 / 2 from by norm_num,
      Real.rpow_add Real.pi_pos 2 (1 / 2), Real.rpow_two, ← Real.sqrt_eq_rpow]
  have hsum : Real.pi ^ 2 * Real.sqrt Real.pi + Real.pi < 22 := by
    nlinarith [hsq, hsqrt, Real.sqrt_nonneg Real.pi]
  have hfinal : (Real.pi ^ (5 / 2 : ℝ) + Real.pi) / 2 < (22 : ℝ) / 2 := by
    rw [hid, div_lt_div_iff_of_pos_right (show (0 : ℝ) < 2 by norm_num)]
    exact hsum
  norm_num at hfinal
  exact hfinal

theorem rho_mul_log_inv_le_one {rho : ℝ} (h0 : 0 < rho) (h1 : rho ≤ 1) :
    rho * Real.log (1 / rho) ≤ 1 := by
  have hu : 0 ≤ -Real.log rho := by
    rw [Left.nonneg_neg_iff]
    exact Real.log_nonpos h0.le h1
  have hexp : -Real.log rho + 1 ≤ Real.exp (-Real.log rho) :=
    Real.add_one_le_exp (-Real.log rho)
  have hden : 0 < Real.exp (-Real.log rho) := Real.exp_pos _
  have hinv : 1 / rho = Real.exp (-Real.log rho) := by
    rw [Real.exp_neg, ← Real.exp_log h0]
    simp
  have hlog_inv : Real.log (1 / rho) = -Real.log rho := by
    rw [hinv, Real.log_exp]
  have hrho : Real.exp (Real.log rho) = 1 / Real.exp (-Real.log rho) := by
    rw [Real.exp_neg, one_div, inv_inv]
  have hrho_mul : rho * Real.exp (-Real.log rho) = 1 := by
    rw [← hinv]
    simp [h0.ne']
  have hform : rho * Real.log (1 / rho) =
      rho * Real.log (1 / rho) * Real.exp (-Real.log rho) /
        Real.exp (-Real.log rho) := by
    field_simp
  rw [hform, div_le_iff₀ hden, mul_comm (rho * Real.log (1 / rho))
      (Real.exp (-Real.log rho)),
    ← mul_assoc, mul_comm (Real.exp (-Real.log rho)) rho, hrho_mul, one_mul]
  linarith

/-! ### From the half_line_inv_add_mul_sq-line evaluation to the manuscript's inner constant -/

/-- Doubling the half_line_inv_add_mul_sq-line evaluation gives the whole line. -/
theorem integral_line_inv_add_mul_sq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ x in Ioi (0:ℝ), (a + b * x ^ 2)⁻¹) * 2 = Real.pi / Real.sqrt (a * b) := by
  rw [integral_Ioi_inv_add_mul_sq ha hb]
  have h : 0 < Real.sqrt (a * b) := Real.sqrt_pos.mpr (by positivity)
  field_simp

/-- At the manuscript's inner coefficients `A = 2ρ²/π²` and `B = c·L`, the
whole-line value `π/√(AB)` is `π²/(ρ√(2cL))`.  With `c = 2/(π³κ)` this is the
printed `π^{5/2}√κ/2 · (ρ√L)⁻¹`, and it is the term the assembled route replaces
by the much larger `1/c`. -/
theorem pi_div_sqrt_inner {rho c L : ℝ} (hrho : 0 < rho) (hc : 0 < c) (hL : 0 < L) :
    Real.pi / Real.sqrt (2 / Real.pi ^ 2 * rho ^ 2 * (c * L))
      = Real.pi ^ 2 / (rho * Real.sqrt (2 * c * L)) := by
  have hpi := Real.pi_pos
  have h1 : 2 / Real.pi ^ 2 * rho ^ 2 * (c * L) = rho ^ 2 * (2 * c * L) / Real.pi ^ 2 := by
    ring
  rw [h1, Real.sqrt_div' _ (by positivity), Real.sqrt_mul (by positivity),
    Real.sqrt_sq hrho.le, Real.sqrt_sq hpi.le]
  field_simp

/-! ### The half_line_inv_add_mul_sq-integer power of pi

`π^{5/2} = π²√π` and the numeric bound behind the manuscript's `11`. -/

theorem rpow_five_halves {x : ℝ} (hx : 0 ≤ x) :
    x ^ (5/2 : ℝ) = x ^ 2 * Real.sqrt x := by
  rcases eq_or_lt_of_le hx with rfl | hxpos
  · simp [Real.zero_rpow]
  · rw [show (5/2 : ℝ) = 2 + 1 / 2 by norm_num, Real.rpow_add hxpos,
      Real.rpow_ofNat x 2, ← Real.sqrt_eq_rpow]

theorem pi_rpow_five_halves_lt : Real.pi ^ (5/2 : ℝ) < 18 := by
  rw [rpow_five_halves Real.pi_nonneg]
  have hp : Real.pi < 3.15 := Real.pi_lt_d2
  have hsq : Real.pi ^ 2 < (63 / 20 : ℝ) ^ 2 := by
    nlinarith [hp, Real.pi_pos]
  have hs : Real.sqrt Real.pi < 71 / 40 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 71 / 40),
      Real.lt_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt Real.pi_pos.le]
    nlinarith [hp]
  calc Real.pi ^ 2 * Real.sqrt Real.pi
      < (63 / 20 : ℝ) ^ 2 * (71 / 40) :=
      by nlinarith [hsq, hs]
    _ < 18 := by norm_num

/-! ### The outer piece of the split

Outside `|β| = √ρ` the weight dominates `2β²/π²`, and the tail integral of
`β⁻²` is `1/√ρ`.  This is the second of the manuscript's two pieces, evaluated
rather than bounded. -/

theorem integrableOn_inv_sq {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun b : ℝ => (b ^ 2)⁻¹) (Ioi c) := by
  have h := integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) hc
  refine h.congr_fun ?_ measurableSet_Ioi
  intro b hb
  have hb0 : 0 < b := lt_trans hc (mem_Ioi.mp hb)
  show b ^ (-2 : ℝ) = (b ^ 2)⁻¹
  rw [Real.rpow_neg hb0.le]
  congr 1
  rw [show ((2:ℝ)) = ((2:ℕ) : ℝ) by norm_num, Real.rpow_natCast]

theorem outer_piece_le {rho : ℝ} (hrho : 0 < rho) {Phi : ℝ → ℝ}
    (hpos : ∀ b, 0 < Phi b)
    (h3 : ∀ b, 2 / Real.pi ^ 2 * b ^ 2 ≤ Phi b) :
    ∫ b in Ioi (Real.sqrt rho), (Phi b)⁻¹
      ≤ Real.pi ^ 2 / 2 * (Real.sqrt rho)⁻¹ := by
  have hs : 0 < Real.sqrt rho := Real.sqrt_pos.mpr hrho
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hbound : ∀ b ∈ Ioi (Real.sqrt rho),
      (Phi b)⁻¹ ≤ Real.pi ^ 2 / 2 * (b ^ 2)⁻¹ := by
    intro b hb
    have hb0 : 0 < b := lt_trans hs (mem_Ioi.mp hb)
    have hq : (0:ℝ) < 2 / Real.pi ^ 2 * b ^ 2 := by positivity
    have hle := inv_anti₀ hq (h3 b)
    refine hle.trans (le_of_eq ?_)
    field_simp
  calc ∫ b in Ioi (Real.sqrt rho), (Phi b)⁻¹
      ≤ ∫ b in Ioi (Real.sqrt rho), Real.pi ^ 2 / 2 * (b ^ 2)⁻¹ :=
        integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun b => (inv_pos.mpr (hpos b)).le)
          ((integrableOn_inv_sq hs).const_mul _)
          (ae_restrict_of_forall_mem measurableSet_Ioi hbound)
    _ = Real.pi ^ 2 / 2 * (Real.sqrt rho)⁻¹ := by
        rw [integral_const_mul, integral_Ioi_inv_sq hs]

/-! ### The inner piece of the split

On `|β| ≤ √ρ` the weight dominates `A + Bβ²`, and the integral of the
reciprocal quadratic over that interval is at most its integral over the whole
line, `π/√(AB)`.  The whole-line value is taken as a hypothesis here; it is the
doubling of `integral_Ioi_inv_add_mul_sq`. -/

theorem inner_piece_le {rho A B : ℝ} (hrho : 0 < rho) (hA : 0 < A) (hB : 0 < B)
    {Phi : ℝ → ℝ} (hpos : ∀ b, 0 < Phi b)
    (hint : Integrable (fun x : ℝ => (A + B * x ^ 2)⁻¹))
    (hval : (∫ x : ℝ, (A + B * x ^ 2)⁻¹) = Real.pi / Real.sqrt (A * B))
    (hin : ∀ b, |b| ≤ Real.sqrt rho → A + B * b ^ 2 ≤ Phi b) :
    ∫ b in Ioo (-Real.sqrt rho) (Real.sqrt rho), (Phi b)⁻¹
      ≤ Real.pi / Real.sqrt (A * B) := by
  have hs : 0 < Real.sqrt rho := Real.sqrt_pos.mpr hrho
  have hnn : ∀ x : ℝ, 0 ≤ (A + B * x ^ 2)⁻¹ := fun x => by positivity
  have hcmp : ∀ b ∈ Ioo (-Real.sqrt rho) (Real.sqrt rho),
      (Phi b)⁻¹ ≤ (A + B * b ^ 2)⁻¹ := by
    intro b hb
    have habs : |b| ≤ Real.sqrt rho := by
      rw [abs_le]; exact ⟨hb.1.le, hb.2.le⟩
    exact inv_anti₀ (by positivity) (hin b habs)
  calc ∫ b in Ioo (-Real.sqrt rho) (Real.sqrt rho), (Phi b)⁻¹
      ≤ ∫ b in Ioo (-Real.sqrt rho) (Real.sqrt rho), (A + B * b ^ 2)⁻¹ :=
        integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun b => (inv_pos.mpr (hpos b)).le)
          (hint.integrableOn)
          (ae_restrict_of_forall_mem measurableSet_Ioo hcmp)
    _ ≤ ∫ x : ℝ, (A + B * x ^ 2)⁻¹ :=
        setIntegral_le_integral hint (Filter.Eventually.of_forall hnn)
    _ = Real.pi / Real.sqrt (A * B) := hval

/-! ### The reciprocal quadratic over the whole line

This discharges the hypothesis of `inner_piece_le`. -/

theorem half_line_inv_add_mul_sq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ x in Ioi (0:ℝ), (a + b * x ^ 2)⁻¹) = Real.pi / (2 * Real.sqrt (a * b)) := by
  set c := √(b / a) with hc_def
  have hc : 0 < c := Real.sqrt_pos.mpr (by positivity)
  have hac : a * c = √(a * b) := by
    calc a * c = a * (√b / √a) := by rw [hc_def, Real.sqrt_div' b ha.le]
      _ = √a * √b := by field_simp; rw [Real.sq_sqrt ha.le]
      _ = √(a * b) := by rw [Real.sqrt_mul ha.le b]
  have hfun : ∀ x : ℝ, (a + b * x ^ 2)⁻¹ = a⁻¹ * (1 + (c * x) ^ 2)⁻¹ := by
    intro x
    rw [hc_def, mul_pow, Real.sq_sqrt (le_of_lt (div_pos hb ha))]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi (fun x _ => hfun x)]
  rw [integral_const_mul _ _, integral_comp_mul_left_Ioi
    (fun u : ℝ => (1 + u ^ 2)⁻¹) 0 hc]
  simp only [smul_eq_mul, mul_zero]
  rw [integral_Ioi_inv_one_add_sq, ← hac]
  field_simp
  simp

theorem integrable_inv_add_mul_sq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Integrable (fun x : ℝ => (a + b * x ^ 2)⁻¹) := by
  set c := √(b / a) with hc_def
  have hc : 0 < c := Real.sqrt_pos.mpr (by positivity)
  have hfun : ∀ x : ℝ, (a + b * x ^ 2)⁻¹ = a⁻¹ * (1 + (c * x) ^ 2)⁻¹ := by
    intro x
    rw [hc_def, mul_pow, Real.sq_sqrt (le_of_lt (div_pos hb ha))]
    field_simp
  convert (integrable_inv_one_add_sq.comp_mul_left' hc.ne').const_mul a⁻¹ using 1
  funext x
  exact hfun x

theorem integral_univ_inv_add_mul_sq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ x : ℝ, (a + b * x ^ 2)⁻¹) = Real.pi / Real.sqrt (a * b) := by
  have hint := integrable_inv_add_mul_sq ha hb
  have hfun : ∀ x : ℝ, (a + b * x ^ 2)⁻¹ = (a + b * (-x) ^ 2)⁻¹ := by
    intro x; congr 1; ring
  have hneg : (∫ x in Iic (0:ℝ), (a + b * x ^ 2)⁻¹) =
      ∫ x in Ioi (0:ℝ), (a + b * x ^ 2)⁻¹ := by
    calc (∫ x in Iic (0:ℝ), (a + b * x ^ 2)⁻¹)
        = ∫ x in Iic (0:ℝ), (a + b * (-x) ^ 2)⁻¹ :=
          setIntegral_congr_fun measurableSet_Iic (fun x _ => hfun x)
      _ = ∫ x in Ioi (-0:ℝ), (a + b * x ^ 2)⁻¹ :=
          integral_comp_neg_Iic 0 (fun x : ℝ => (a + b * x ^ 2)⁻¹)
      _ = ∫ x in Ioi (0:ℝ), (a + b * x ^ 2)⁻¹ := by simp
  rw [← setIntegral_univ, ← Set.Iic_union_Ioi (a := (0:ℝ)),
    setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
      hint.integrableOn hint.integrableOn,
    hneg, half_line_inv_add_mul_sq ha hb]
  field_simp [Real.sqrt_mul ha.le b]
  norm_num

/-! ### The exact frequency integral

`∫₀^{r₀} da/(a(1+log(1/a))^{3/2}) = 2/√(1+log(1/r₀))`, the evaluation the
manuscript performs where the assembled three-region route bounds instead. -/

theorem integral_Ioo_inv_mul_logPow {r0 : ℝ} (hr0 : 0 < r0) (hr1 : r0 < 1) :
    (∫ a in Ioo (0:ℝ) r0, (a * (1 + Real.log (1 / a)) ^ (3/2 : ℝ))⁻¹)
      = 2 / Real.sqrt (1 + Real.log (1 / r0)) := by
  have hL : 0 < Real.log (1 / r0) :=
    Real.log_pos (one_lt_one_div hr0 hr1)
  set L := Real.log (1 / r0) with hLdef
  have hbaseL : 0 < 1 + L := by positivity
  have himage : (fun x : ℝ => -Real.log x) '' Ioo 0 r0 = Ioi L := by
    have hlogL : L = -Real.log r0 := by
      rw [hLdef, one_div]
      exact Real.log_inv r0
    ext u
    simp only [mem_image, mem_Ioo, mem_Ioi]
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨hx0, hxr⟩ := mem_Ioo.mp hx
      rw [hlogL]
      exact neg_lt_neg (Real.log_lt_log hx0 hxr)
    · intro hu
      refine ⟨Real.exp (-u), mem_Ioo.mpr ⟨Real.exp_pos _, ?_⟩, by simp⟩
      have hlu : -u < Real.log r0 := by
        rw [hlogL] at hu
        linarith
      exact (Real.lt_log_iff_exp_lt hr0).mp hlu
  have hint : IntegrableOn (fun u : ℝ => (1 + u) ^ (-(3/2) : ℝ)) (Ioi L) :=
    integrableOn_add_rpow_Ioi_of_lt (a := (-(3/2) : ℝ)) (m := 1)
      (show (-(3/2) : ℝ) < -1 by norm_num)
      (by linarith)
      |>.congr_fun (fun u _ => by rw [add_comm]) measurableSet_Ioi
  have hderivfun : ∀ x ∈ Ioo 0 r0, HasDerivWithinAt
      (fun y : ℝ => -Real.log y) (-(x : ℝ)⁻¹) (Ioo 0 r0) x :=
    fun x hx => ((Real.hasDerivAt_log (ne_of_gt hx.1)).fun_neg).hasDerivWithinAt
  have hsub := integral_image_eq_integral_deriv_smul_of_antitone
    (s := Ioo (0:ℝ) r0) measurableSet_Ioo hderivfun
    (fun x hx y hy hxy => by
      simp only [mem_Ioo] at hx hy
      exact neg_le_neg (Real.log_le_log hx.1 hxy))
    (fun u : ℝ => (1 + u) ^ (-(3/2) : ℝ))
  rw [himage] at hsub
  have hcongr : ∀ x ∈ Ioo 0 r0,
      (x : ℝ)⁻¹ * (1 + -Real.log x) ^ (-(3/2) : ℝ) =
        (x * (1 + Real.log (1 / x)) ^ (3/2 : ℝ))⁻¹ := by
    rintro x ⟨hx0, hx1⟩
    simp only [one_div, Real.log_inv]
    have hbase : 0 < 1 - Real.log x := by
      linarith [Real.log_neg hx0 (lt_trans hx1 hr1)]
    have hexpr : 1 + -Real.log x = 1 - Real.log x := by ring
    have hrpow : (1 - Real.log x) ^ (-(3/2) : ℝ) =
        ((1 - Real.log x) ^ ((3/2) : ℝ))⁻¹ := by
      rw [Real.rpow_neg hbase.le (3/2 : ℝ)]
    rw [hexpr, hrpow]
    field_simp
  have hsmul := setIntegral_congr_fun (μ := volume) measurableSet_Ioo hcongr
  have hsmul2 : ∫ x in Ioo (0:ℝ) r0, - -x⁻¹ • (1 + -Real.log x) ^ (-(3/2) : ℝ)
      = ∫ x in Ioo (0:ℝ) r0, x⁻¹ * (1 + -Real.log x) ^ (-(3/2) : ℝ) :=
    setIntegral_congr_fun (μ := volume) measurableSet_Ioo
    (fun x hx => by
      simp only [smul_eq_mul, neg_neg]
    )
  have hGder : ∀ u ∈ Ioi L,
      HasDerivAt (fun v : ℝ => (1 + v) ^ (-(1/2) : ℝ) * (-2))
        ((1 + u) ^ (-(3/2) : ℝ)) u := by
    intro u hu
    have huL : L < u := mem_Ioi.mp hu
    have hbase : 0 < 1 + u := by linarith
    have hpow := Real.hasDerivAt_rpow_const
      (p := -(1/2 : ℝ)) (Or.inl (ne_of_gt hbase))
    have hadd : HasDerivAt (fun v : ℝ => 1 + v) 1 u :=
      (hasDerivAt_id u).const_add 1
    have hcomp := hpow.comp u hadd
    have h := hcomp.mul_const (-2)
    refine h.congr_deriv ?_
    rw [show (-(1/2) - 1 : ℝ) = (-(3/2) : ℝ) by ring]
    ring
  have hGlim : Filter.Tendsto (fun v : ℝ => (1 + v) ^ (-(1/2) : ℝ) * (-2)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop
      (show 0 < (1/2 : ℝ) by norm_num)).mul_const (-2)
    have hid : Filter.Tendsto (fun v : ℝ => 1 + v) atTop atTop := by
      exact Filter.tendsto_atTop_atTop.mpr
        (fun b => ⟨b - 1, by intro x hx; linarith⟩)
    simpa using h.comp hid
  have hpowcont : ContinuousOn (fun v : ℝ => (1 + v) ^ (-(1/2) : ℝ)) (Ici L) := by
    refine (continuous_const.add continuous_id).continuousOn.rpow_const ?_
    intro x hx
    have hxL : L ≤ x := mem_Ici.mp hx
    have hxpos : 0 < 1 + x := by
      linarith [hL, hxL]
    exact Or.inl (ne_of_gt hxpos)
  have hcont : ContinuousWithinAt (fun v : ℝ => (1 + v) ^ (-(1/2) : ℝ) * (-2)) (Ici L) L := by
    refine (hpowcont.mul continuousOn_const).continuousWithinAt left_mem_Ici
  have hIoi := integral_Ioi_of_hasDerivAt_of_tendsto hcont hGder hint hGlim
  rw [hsmul.symm, hsmul2.symm, hsub.symm, hIoi]
  rw [Real.rpow_neg hbaseL.le, Real.sqrt_eq_rpow]
  ring

/-! ### The split, with no hypotheses left

`integral_univ_inv_add_mul_sq` discharges the whole-line value that
`inner_piece_le` took as an assumption, so the inner bound is now
unconditional. -/

theorem inner_piece_le' {rho A B : ℝ} (hrho : 0 < rho) (hA : 0 < A) (hB : 0 < B)
    {Phi : ℝ → ℝ} (hpos : ∀ b, 0 < Phi b)
    (hin : ∀ b, |b| ≤ Real.sqrt rho → A + B * b ^ 2 ≤ Phi b) :
    ∫ b in Ioo (-Real.sqrt rho) (Real.sqrt rho), (Phi b)⁻¹
      ≤ Real.pi / Real.sqrt (A * B) :=
  inner_piece_le hrho hA hB hpos (integrable_inv_add_mul_sq hA hB)
    (integral_univ_inv_add_mul_sq hA hB) hin

/-- **The two pieces together.**  With the manuscript's inner coefficients the
sum is `π/(2√(2cL)·ρ) + π/(2√ρ)` after the `1/(2π)` normalization, against the
assembled route's `(π² + 1/c)/(ρ√L)`. -/
theorem split_sum_le {rho A B : ℝ} (hrho : 0 < rho) (hA : 0 < A) (hB : 0 < B)
    {Phi : ℝ → ℝ} (hpos : ∀ b, 0 < Phi b)
    (hin : ∀ b, |b| ≤ Real.sqrt rho → A + B * b ^ 2 ≤ Phi b)
    (hout : ∀ b, 2 / Real.pi ^ 2 * b ^ 2 ≤ Phi b) :
    (∫ b in Ioo (-Real.sqrt rho) (Real.sqrt rho), (Phi b)⁻¹)
        + ∫ b in Ioi (Real.sqrt rho), (Phi b)⁻¹
      ≤ Real.pi / Real.sqrt (A * B) + Real.pi ^ 2 / 2 * (Real.sqrt rho)⁻¹ :=
  add_le_add (inner_piece_le' hrho hA hB hpos hin) (outer_piece_le hrho hpos hout)

end Manhattan.V4.Beta
