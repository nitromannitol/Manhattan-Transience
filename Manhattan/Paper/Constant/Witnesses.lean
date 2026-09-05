import Manhattan.Paper.Constant.GreenConstant

/-!
# The paper's constant, part 3: non-degeneracy

Anti-vacuity for the constants, in the shape the sibling files use.

* `frequencyConstant_gt` / `frequencyConstant_lt` pin the composed
  fixed-frequency constant strictly between two numerals, so it is a genuine
  real and not a junk value, and so the bounds proved about it are not
  vacuously about `⊤` or `0`.

* `tightened_lt_v4` and `move3_rhs_strict` are **strict**: the constant this
  file composes is strictly smaller than the one `Manhattan/V4/` composes, at
  every frequency.  No link in this file is an `X ≤ X`.

* `green_constant_gt_paper` is the honest statement of the residual gap: what
  the Version 4 chain proves for `∫₀^∞ p̄_t(0,0) dt` exceeds the manuscript's
  `2048` by more than a factor `10⁵`.

* `greenDensity_integrable`, `annulusWedgeX_integrable`,
  `annulusWedgeY_integrable`, `logSqrt_intervalIntegrable` and
  `logarithmicTail_eq_two` record that every Bochner or interval integral in
  the composed chain carries an integrability certificate.  The remaining
  integrals of the chain are `ℝ≥0∞`-valued (`∫⁻`), always defined, and their
  monotone-limit step uses the measurability hypothesis of
  `MeasureTheory.lintegral_liminf_le`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Manhattan.Paper.Constant

open Manhattan.V4 Manhattan.V4.Frequency

/-! ### The constant is a genuine number -/

theorem frequencyConstant_gt : (7389000 : ℝ) < frequencyConstant := by
  refine lt_of_lt_of_le ?_ ((le_max_right 1 _).trans (le_max_left _ _))
  nlinarith [pi_sq_ge, v4Constant_ge, v4Constant_pos]

theorem frequencyConstant_lt : frequencyConstant < 7400000 := by
  refine lt_of_le_of_lt ?_ (by norm_num : (7390000 : ℝ) < 7400000)
  unfold frequencyConstant
  refine max_le (max_le (by norm_num) ?_)
    (outerRegionConstant_quarter_le.trans (by norm_num))
  nlinarith [v4Constant_le, v4Constant_pos, pi_sq_le]

/-! ### The tightening is strict -/

/-- The Move 3 constant of this file is strictly below the one of
`Manhattan.V4.Frequency.move3_bound`. -/
theorem tightened_lt_v4 :
    10 * Real.pi ^ 2 * v4Constant < 8 * Real.pi ^ 3 * v4Constant := by
  have hpi : (3:ℝ) < Real.pi := Real.pi_gt_three
  have hkey : 10 * Real.pi ^ 2 < 8 * Real.pi ^ 3 := by
    nlinarith [mul_pos (pow_pos Real.pi_pos 2) (by linarith : (0:ℝ) < 8 * Real.pi - 10)]
  exact mul_lt_mul_of_pos_right hkey v4Constant_pos

/-- ... and therefore so is the whole right-hand side of Move 3, at every
frequency and every `λ > 0`.  Strict, so this chain contains no
`X ≤ X`. -/
theorem move3_rhs_strict {lambda : ℝ} (hlambda : 0 < lambda) (p : Fin 2 → ℝ) :
    max 1 (10 * Real.pi ^ 2 * v4Constant) * v4Majorant lambda p
      < max 1 (8 * Real.pi ^ 3 * v4Constant) * v4Majorant lambda p := by
  have hmpos : 0 < v4Majorant lambda p := v4Majorant_pos hlambda p
  have hlow : (1:ℝ) ≤ 10 * Real.pi ^ 2 * v4Constant := by
    nlinarith [pi_sq_ge, v4Constant_ge, v4Constant_pos]
  have hstrict := tightened_lt_v4
  rw [max_eq_right hlow, max_eq_right (by linarith : (1:ℝ) ≤ 8 * Real.pi ^ 3 * v4Constant)]
  exact mul_lt_mul_of_pos_right hstrict hmpos

/-! ### The residual gap against the manuscript -/

/-- **The gap, machine-checked.**  The manuscript's `eq:green-explicit` asserts
`∫₀^∞ p̄_t(0,0) dt ≤ 2048`.  The constant the Version 4 chain composes for the
same integral is more than `10⁵` times larger. -/
theorem green_constant_gt_paper :
    (2048 : ℝ) * 100000
      < frequencyConstant + 2 * (8 * frequencyConstant)
          + frequencyConstant * (2 * Real.pi ^ 2 / (99 / 100 : ℝ) ^ 2) := by
  have hF := frequencyConstant_gt
  have hFnn : (0:ℝ) < frequencyConstant := frequencyConstant_pos
  have hcoef : (20.1399 : ℝ) ≤ 2 * Real.pi ^ 2 / (99 / 100 : ℝ) ^ 2 := by
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < (99 / 100 : ℝ) ^ 2)]
    nlinarith [pi_sq_ge]
  nlinarith [mul_le_mul_of_nonneg_left hcoef hFnn.le]

/-- The paper's own number is far below the numeral this file lands, so the
landed numeral is not a restatement of the paper's claim. -/
theorem paper_constant_lt_numeral : (2048 : ℝ) < 275000000 := by norm_num

/-! ### Every integral carries an integrability proof -/

/-- The frequency integral of the concrete Green density. -/
theorem greenDensity_integrable {lambda : ℝ} (hlambda : 0 < lambda) :
    Integrable (Manhattan.Glue.concreteGreenDensity lambda)
      Manhattan.Estimates.torusProductMeasure :=
  Manhattan.Glue.concreteGreenDensity_integrable hlambda

/-- The two square-annulus wedge majorants of the frequency integration. -/
theorem annulusWedgeX_integrable {r0 lambda : ℝ} (hlambda : 0 < lambda) :
    Integrable (Manhattan.Estimates.annulusWedgeX r0 lambda)
      Manhattan.Estimates.torusProductMeasure :=
  Manhattan.Estimates.annulusWedgeX_integrable hlambda

theorem annulusWedgeY_integrable {r0 lambda : ℝ} (hlambda : 0 < lambda) :
    Integrable (Manhattan.Estimates.annulusWedgeY r0 lambda)
      Manhattan.Estimates.torusProductMeasure :=
  Manhattan.Estimates.annulusWedgeY_integrable hlambda

/-- The integrand of `Z_δ`, on every interval away from the origin. -/
theorem logSqrt_intervalIntegrable {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun r : ℝ => Real.sqrt (-Real.log r) / r) volume a b :=
  Manhattan.V4.logSqrt_intervalIntegrable ha hab

/-- The logarithmic tail of the annulus integration is evaluated exactly, not
merely bounded. -/
theorem logarithmicTail_eq_two : Manhattan.Operator.logarithmicTail = 2 :=
  Manhattan.Operator.logarithmicTail_eq_two

/-! ### The fixed-frequency bound is not vacuous -/

/-- At the corner `p = (π, π)` the Version 4 majorant is the explicit positive
number `1/(1 + π²)`, so `v4FrequencyBound_tight_proved` there is a genuine
finite bound and not a statement about `⊤`. -/
theorem v4Majorant_corner :
    v4Majorant 1 ![Real.pi, Real.pi] = 1 / (1 + Real.pi ^ 2) := by
  have hpi : (3:ℝ) < Real.pi := Real.pi_gt_three
  have hmax : Operator.maxFrequency ![Real.pi, Real.pi] = Real.pi := by
    simp [Operator.maxFrequency, abs_of_pos Real.pi_pos]
  have hscale : v4LogScale 1 ![Real.pi, Real.pi] = 1 := by
    unfold v4LogScale Operator.logPos
    rw [hmax, Real.sqrt_one,
      max_eq_right (Real.log_nonpos (by positivity)
        (by rw [div_le_one (by linarith)]; linarith))]
    ring
  unfold v4Majorant
  rw [hscale, hmax, Real.one_rpow]
  norm_num

end Manhattan.Paper.Constant
