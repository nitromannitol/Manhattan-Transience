import Manhattan.Estimates.TargetStatements
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# The one-dimensional resolvent integral

This module proves equation (22) by a tangent half-angle antiderivative. The
one-sided endpoint limits are kept explicit because `tan (r / 2)` is singular
at `r = ±π`.

Paper: `manuscript.tex:860-867`.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace Manhattan.Estimates

noncomputable section

private theorem tendsto_half_nhdsLT_pi :
    Tendsto (fun x : ℝ => x / 2) (𝓝[<] Real.pi) (𝓝[<] (Real.pi / 2)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · exact (tendsto_id.div_const (2 : ℝ)).mono_left inf_le_left
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact (div_lt_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).2 hx

private theorem tendsto_half_nhdsGT_neg_pi :
    Tendsto (fun x : ℝ => x / 2) (𝓝[>] (-Real.pi)) (𝓝[>] (-(Real.pi / 2))) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · simpa only [neg_div] using
      (tendsto_id.div_const (2 : ℝ)).mono_left
        (inf_le_left : 𝓝[>] (-Real.pi) ≤ 𝓝 (-Real.pi))
  · filter_upwards [self_mem_nhdsWithin] with x hx
    calc
      -(Real.pi / 2) = (-Real.pi) / 2 := by ring
      _ < x / 2 := (div_lt_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).2 hx

private theorem lineAntiderivative_hasDerivAt {mu x : ℝ} (hmu : 0 < mu)
    (hx : x ∈ Ioo (-Real.pi) Real.pi) :
    HasDerivAt
      (fun y : ℝ => 2 / Real.sqrt (mu * (mu + 2)) *
        Real.arctan ((mu + 2) / Real.sqrt (mu * (mu + 2)) * Real.tan (y / 2)))
      ((mu + dispersion x)⁻¹) x := by
  have hmu2 : 0 < mu + 2 := by linarith
  have hprod : 0 < mu * (mu + 2) := mul_pos hmu hmu2
  have hsqrt : 0 < Real.sqrt (mu * (mu + 2)) := Real.sqrt_pos.2 hprod
  have hhalf : x / 2 ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [hx.1, hx.2]
  have hcos : Real.cos (x / 2) ≠ 0 := (Real.cos_pos_of_mem_Ioo hhalf).ne'
  have htan : HasDerivAt (fun y : ℝ => Real.tan (y / 2))
      (1 / Real.cos (x / 2) ^ 2 / 2) x := by
    convert (Real.hasDerivAt_tan hcos).comp x ((hasDerivAt_id x).div_const 2) using 1
    ring
  have hinner : HasDerivAt
      (fun y : ℝ => (mu + 2) / Real.sqrt (mu * (mu + 2)) * Real.tan (y / 2))
      ((mu + 2) / Real.sqrt (mu * (mu + 2)) *
        (1 / Real.cos (x / 2) ^ 2 / 2)) x := htan.const_mul _
  have harctan := hinner.arctan
  convert harctan.const_mul (2 / Real.sqrt (mu * (mu + 2))) using 1
  have hsqrtSq : Real.sqrt (mu * (mu + 2)) ^ 2 = mu * (mu + 2) :=
    Real.sq_sqrt hprod.le
  have htrig : dispersion x = 2 * Real.sin (x / 2) ^ 2 := by
    unfold dispersion
    rw [show Real.cos x = Real.cos (2 * (x / 2)) by congr 1; ring,
      Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq (x / 2)]
  field_simp
  rw [htrig, Real.tan_eq_sin_div_cos]
  field_simp
  nlinarith [Real.sin_sq_add_cos_sq (x / 2)]

/-- Equation (22): the normalized line resolvent has its exact closed form. -/
theorem lineResolventIdentity_proved : LineResolventIdentity := by
  intro mu hmu
  have hmu2 : 0 < mu + 2 := by linarith
  have hprod : 0 < mu * (mu + 2) := mul_pos hmu hmu2
  have hsqrt : 0 < Real.sqrt (mu * (mu + 2)) := Real.sqrt_pos.2 hprod
  let F : ℝ → ℝ := fun y => 2 / Real.sqrt (mu * (mu + 2)) *
    Real.arctan ((mu + 2) / Real.sqrt (mu * (mu + 2)) * Real.tan (y / 2))
  have hint : IntervalIntegrable (fun x : ℝ => (mu + dispersion x)⁻¹)
      volume (-Real.pi) Real.pi := by
    apply ContinuousOn.intervalIntegrable
    apply Continuous.continuousOn
    apply Continuous.inv₀
    · exact continuous_const.add (continuous_const.sub Real.continuous_cos)
    · intro x hx
      exact (ne_of_gt (add_pos_of_pos_of_nonneg hmu (dispersion_nonneg x))) hx
  have hleftTan : Tendsto (fun x : ℝ => Real.tan (x / 2))
      (𝓝[>] (-Real.pi)) atBot :=
    Real.tendsto_tan_neg_pi_div_two.comp tendsto_half_nhdsGT_neg_pi
  have hrightTan : Tendsto (fun x : ℝ => Real.tan (x / 2))
      (𝓝[<] Real.pi) atTop :=
    Real.tendsto_tan_pi_div_two.comp tendsto_half_nhdsLT_pi
  have hcpos : 0 < (mu + 2) / Real.sqrt (mu * (mu + 2)) := div_pos hmu2 hsqrt
  have hleftInner : Tendsto
      (fun x : ℝ => (mu + 2) / Real.sqrt (mu * (mu + 2)) * Real.tan (x / 2))
      (𝓝[>] (-Real.pi)) atBot := (tendsto_const_mul_atBot_of_pos hcpos).2 hleftTan
  have hrightInner : Tendsto
      (fun x : ℝ => (mu + 2) / Real.sqrt (mu * (mu + 2)) * Real.tan (x / 2))
      (𝓝[<] Real.pi) atTop := (tendsto_const_mul_atTop_of_pos hcpos).2 hrightTan
  have hleft : Tendsto F (𝓝[>] (-Real.pi))
      (𝓝 ((2 / Real.sqrt (mu * (mu + 2))) * (-(Real.pi / 2)))) := by
    exact ((Real.tendsto_arctan_atBot.comp hleftInner).mono_right inf_le_left).const_mul _
  have hright : Tendsto F (𝓝[<] Real.pi)
      (𝓝 ((2 / Real.sqrt (mu * (mu + 2))) * (Real.pi / 2))) := by
    exact ((Real.tendsto_arctan_atTop.comp hrightInner).mono_right inf_le_left).const_mul _
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    (neg_lt_self Real.pi_pos) (fun x hx => lineAntiderivative_hasDerivAt hmu hx)
    hint hleft hright
  rw [torusIntegral, torus,
    ← intervalIntegral.integral_of_le (le_of_lt (neg_lt_self Real.pi_pos))]
  rw [hi]
  simp only [smul_eq_mul]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hsqrtNe : Real.sqrt (mu * (mu + 2)) ≠ 0 := hsqrt.ne'
  field_simp
  ring

end

end Manhattan.Estimates
