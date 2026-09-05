import Manhattan.Paper.Constant.Move3
import Manhattan.Glue.Annealed

/-!
# The paper's constant, part 2: the explicit Green bound Lean proves

`results/01-transience/manuscript.tex`, `eq:green-explicit`, asserts

    ∫₀^∞ p̄_t(0,0) dt ≤ 2048 .

That number is correct on the manuscript's own terms; see
for the re-derivation.  This file records, as a
machine-checked numeral rather than as prose, what the Version 4 Lean chain
actually delivers for the same integral.

Three constants compose.

* `Manhattan.V4.v4Constant = 60 + 40(π² + 60π³) ≈ 7.4870 · 10⁴` is Move 1's
  effective-energy coefficient.  The manuscript's `eq:effective-energy` has
  `16` in the same slot.  This part cannot change it: it is proved inside
  `Manhattan/V4/`, which is frozen for this part.

* `frequencyConstant = max (max 1 (10π² · v4Constant)) (outerRegionConstant (1/4))`
  is the fixed-frequency constant, `Manhattan.Paper.Constant.v4FrequencyBound_tight`
  at `r₀ = 1/4`.  It is pinned between `7389000` and `7400000` below.  The
  manuscript's counterpart is `C = 2048` in `prop:frequency`.

* The three-region frequency integration multiplies by `17 + 2π²/r₀²`, with
  `r₀` the region-splitting radius, free in `(0,1)`.  `Manhattan/V4/` runs it
  at `r₀ = 1/2`, giving `17 + 8π² ≈ 95.96`; at `r₀ = 99/100` it is
  `≈ 37.14`.  The manuscript's counterpart is `2^{7/2}/(π²√(1+log 4)) ≈ 0.742`
  together with the additive `1/π² + log(4π) ≈ 2.63`.

The composed numeral is `2.75 · 10⁸`, about `1.34 · 10⁵` times the paper's
`2048`.  `Manhattan/Paper/Constant/Witnesses.lean` records that gap as a strict
machine-checked inequality.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace Manhattan.Paper.Constant

open Manhattan.V4 Manhattan.V4.Frequency

/-- The tightened fixed-frequency constant of the Version 4 chain at
`r₀ = 1/4`.  `Manhattan.V4.v4FrequencyBound_proved` uses
`max (max 1 (8π³ · v4Constant)) (outerRegionConstant (1/4))` instead. -/
def frequencyConstant : ℝ :=
  max (max 1 (10 * Real.pi ^ 2 * v4Constant)) (outerRegionConstant (1 / 4))

theorem frequencyConstant_pos : 0 < frequencyConstant :=
  lt_of_lt_of_le one_pos ((le_max_left 1 _).trans (le_max_left _ _))

/-- **The tightened fixed-frequency bound, unconditionally.** -/
theorem v4FrequencyBound_tight_proved : V4FrequencyBound frequencyConstant :=
  v4FrequencyBound_tight (by norm_num) le_rfl v4Constant_pos
    (v4Move2Supply_proved (by norm_num) le_rfl)

/-! ### The numerals -/

theorem pi_sq_le : Real.pi ^ 2 ≤ 9.86961 := by
  nlinarith [Real.pi_lt_d6, Real.pi_pos]

theorem pi_sq_ge : (9.8696 : ℝ) ≤ Real.pi ^ 2 := by
  nlinarith [Real.pi_gt_d6, Real.pi_pos]

theorem pi_cube_le : Real.pi ^ 3 ≤ 31.0063 := by
  nlinarith [Real.pi_lt_d6, Real.pi_pos, pi_sq_le]

theorem pi_cube_ge : (31.0062 : ℝ) ≤ Real.pi ^ 3 := by
  nlinarith [Real.pi_gt_d6, Real.pi_pos, pi_sq_ge]

/-- The Move 1 constant of Version 4, to five significant figures. -/
theorem v4Constant_le : v4Constant ≤ 74870 := by
  unfold v4Constant
  nlinarith [pi_sq_le, pi_cube_le]

theorem v4Constant_ge : (74869 : ℝ) ≤ v4Constant := by
  unfold v4Constant
  nlinarith [pi_sq_ge, pi_cube_ge]

/-- The complementary region contributes `≈ 82.63`, far below the improvement
region's constant, so it never binds. -/
theorem outerRegionConstant_quarter_le : outerRegionConstant (1 / 4 : ℝ) ≤ 83 := by
  have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlog2pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog4 : Real.log (1 / (1/4 : ℝ)) = 2 * Real.log 2 := by
    norm_num
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  have hx : (1 : ℝ) + 4 * Real.log (1 / (1/4 : ℝ)) ≤ 6.5451774464 := by
    rw [hlog4]; linarith
  have hx1 : (1:ℝ) ≤ 1 + 4 * Real.log (1 / (1/4 : ℝ)) := by
    rw [hlog4]; linarith
  have hxpow : (1 + 4 * Real.log (1 / (1/4 : ℝ))) ^ (3/2 : ℝ) ≤ 16.746 := by
    rw [rpow_three_halves (x := 1 + 4 * Real.log (1 / (1/4 : ℝ))) (by linarith)]
    have hsq : Real.sqrt (1 + 4 * Real.log (1 / (1/4 : ℝ))) ≤ 2.5585 := by
      nlinarith [Real.sq_sqrt (by linarith : (0:ℝ) ≤ 1 + 4 * Real.log (1 / (1/4 : ℝ))),
        Real.sqrt_nonneg (1 + 4 * Real.log (1 / (1/4 : ℝ)))]
    nlinarith [Real.sqrt_nonneg (1 + 4 * Real.log (1 / (1/4 : ℝ)))]
  unfold outerRegionConstant
  refine max_le (by norm_num) ?_
  nlinarith [pi_sq_le, hxpow, Real.pi_pos]

/-- The fixed-frequency constant of the Version 4 chain, pinned above. -/
theorem frequencyConstant_le : frequencyConstant ≤ 7400000 := by
  unfold frequencyConstant
  refine max_le (max_le (by norm_num) ?_)
    (outerRegionConstant_quarter_le.trans (by norm_num))
  nlinarith [v4Constant_le, v4Constant_pos, pi_sq_le]

/-- ... and pinned below, so it is a genuine number and not a junk value. -/
theorem frequencyConstant_ge : (7389000 : ℝ) ≤ frequencyConstant := by
  refine le_trans ?_ ((le_max_right 1 _).trans (le_max_left _ _))
  nlinarith [pi_sq_ge, v4Constant_ge, v4Constant_pos]

/-! ### The frequency integral -/

/-- The frequency integral of the concrete Green density, uniformly in
`λ ∈ (0,1]`, with the three regions split at `r₀ = 99/100`.  `Manhattan/V4/`
runs the same integration at `r₀ = 1/2`, where the outer region alone costs
`8π² ≈ 78.96` instead of `≈ 20.14`. -/
theorem uniform_green_tight {lambda : ℝ} (hlambda : 0 < lambda) (hlambda1 : lambda ≤ 1) :
    Manhattan.Estimates.normalizedFrequencyIntegral
        (Manhattan.Glue.concreteGreenDensity lambda)
      ≤ frequencyConstant + 2 * (8 * frequencyConstant)
          + frequencyConstant * (2 * Real.pi ^ 2 / (99 / 100 : ℝ) ^ 2) :=
  uniform_green_bound_of_v4Bound
    (fun l => Manhattan.Estimates.normalizedFrequencyIntegral
      (Manhattan.Glue.concreteGreenDensity l))
    Manhattan.Glue.concreteGreenDensity (99 / 100) frequencyConstant
    (by norm_num) (by norm_num) frequencyConstant_pos.le
    Manhattan.Glue.concreteGreenDensity_measurable
    Manhattan.Glue.concreteGreenDensity_nonneg
    (fun _ _ _ => le_rfl)
    (fun l hl hl1 z hz1 hz2 => by
      rw [Manhattan.Glue.concreteGreenDensity_eq_resolventQuadratic hl]
      exact v4FrequencyBound_tight_proved l hl hl1 (Manhattan.Glue.concreteFrequency z) hz1 hz2)
    hlambda hlambda1

/-- The manuscript's `∫_{T²} r_λ(p) dm(p)`, as an explicit numeral, uniformly
in `λ ∈ (0,1]`.  The manuscript's own bound on the same quantity is `2048`
(`thm:annealed`, whose proof in fact gives `< 1825`). -/
theorem uniform_green_numeral {lambda : ℝ} (hlambda : 0 < lambda) (hlambda1 : lambda ≤ 1) :
    Manhattan.Estimates.normalizedFrequencyIntegral
        (Manhattan.Glue.concreteGreenDensity lambda) ≤ 275000000 := by
  refine (uniform_green_tight hlambda hlambda1).trans ?_
  have hFnn : (0:ℝ) ≤ frequencyConstant := frequencyConstant_pos.le
  have hcoef : 2 * Real.pi ^ 2 / (99 / 100 : ℝ) ^ 2 ≤ 20.14001 := by
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < (99 / 100 : ℝ) ^ 2)]
    nlinarith [pi_sq_le]
  have hmul : frequencyConstant * (2 * Real.pi ^ 2 / (99 / 100 : ℝ) ^ 2)
      ≤ frequencyConstant * 20.14001 := mul_le_mul_of_nonneg_left hcoef hFnn
  linarith [frequencyConstant_le]

/-- For comparison, the numeral the **untightened** Version 4 route composes:
`Manhattan.V4.v4FrequencyBound_proved` through
`Manhattan.V4.Frequency.uniform_green_bound_of_v4FrequencyBound`, whose region
split is at `r₀ = 1/2`.  The two tightenings of this part are worth a factor
`6.49`. -/
theorem uniform_green_numeral_v4 {lambda : ℝ} (hlambda : 0 < lambda) (hlambda1 : lambda ≤ 1) :
    Manhattan.Estimates.normalizedFrequencyIntegral
        (Manhattan.Glue.concreteGreenDensity lambda) ≤ 1790000000 := by
  have hC : (0:ℝ) ≤ max (max 1 (8 * Real.pi ^ 3 * v4Constant))
      (outerRegionConstant (1 / 4)) :=
    zero_le_one.trans ((le_max_left 1 _).trans (le_max_left _ _))
  refine (uniform_green_bound_of_v4FrequencyBound hC v4FrequencyBound_proved
    hlambda hlambda1).trans ?_
  set C := max (max 1 (8 * Real.pi ^ 3 * v4Constant))
    (outerRegionConstant (1 / 4)) with hCdef
  have hCle : C ≤ 18580000 := by
    rw [hCdef]
    refine max_le (max_le (by norm_num) ?_)
      (outerRegionConstant_quarter_le.trans (by norm_num))
    nlinarith [v4Constant_le, v4Constant_pos, pi_cube_le]
  have hcoef : 2 * Real.pi ^ 2 / (1 / 2 : ℝ) ^ 2 ≤ 78.95688 := by
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < (1 / 2 : ℝ) ^ 2)]
    nlinarith [pi_sq_le]
  have hmul : C * (2 * Real.pi ^ 2 / (1 / 2 : ℝ) ^ 2) ≤ C * 78.95688 :=
    mul_le_mul_of_nonneg_left hcoef hC
  linarith

/-! ### Removing the damping -/

/-- The undamped bound with the constant kept explicit.  This is the Fatou calc
of `Manhattan.Glue.annealedGreenBound_of_uniform_damped` with the existential
over the constant dropped, so that the number survives to the conclusion. -/
theorem undamped_le_of_uniform_damped (C : ℝ≥0∞)
    (hbound : ∀ lambda : ℝ, 0 < lambda → lambda ≤ 1 →
      ∫⁻ t in Ici (0:ℝ),
        ENNReal.ofReal (Real.exp (-lambda * t)) *
          Manhattan.annealedContinuousKernel t 0 0 ≤ C) :
    (∫⁻ t in Ici (0:ℝ), Manhattan.annealedContinuousKernel t 0 0) ≤ C := by
  let lambda : ℕ → ℝ := fun n => ((n + 1 : ℕ) : ℝ)⁻¹
  let f : ℕ → ℝ → ℝ≥0∞ := fun n t =>
    ENNReal.ofReal (Real.exp (-lambda n * t)) *
      Manhattan.annealedContinuousKernel t 0 0
  have hlambdaPos (n : ℕ) : 0 < lambda n := by
    dsimp [lambda]
    positivity
  have hlambdaOne (n : ℕ) : lambda n ≤ 1 := by
    dsimp [lambda]
    exact inv_le_one_of_one_le₀ (by norm_num)
  have hmeas (n : ℕ) : Measurable (f n) := by
    apply Measurable.mul
    · exact ENNReal.continuous_ofReal.measurable.comp (by fun_prop)
    · exact Manhattan.measurable_annealedContinuousKernel 0 0
  have hlambdaTendsto : Tendsto lambda atTop (𝓝 0) := by
    simpa only [lambda, Nat.cast_add, Nat.cast_one, inv_eq_one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0))
  have hf (t : ℝ) : Tendsto (fun n => f n t) atTop
      (𝓝 (Manhattan.annealedContinuousKernel t 0 0)) := by
    have hexp : Tendsto (fun n => Real.exp (-lambda n * t)) atTop (𝓝 1) := by
      have harg : Tendsto (fun n => -lambda n * t) atTop (𝓝 0) := by
        simpa using hlambdaTendsto.neg.mul_const t
      exact Real.tendsto_exp_nhds_zero_nhds_one.comp harg
    simpa [f] using ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal hexp)
      (b := Manhattan.annealedContinuousKernel t 0 0) (Or.inl (by norm_num))
  calc
    ∫⁻ t in Ici (0:ℝ), Manhattan.annealedContinuousKernel t 0 0 =
        ∫⁻ t in Ici (0:ℝ), liminf (fun n => f n t) atTop := by
          apply setLIntegral_congr_fun measurableSet_Ici
          intro t _
          exact (hf t).liminf_eq.symm
    _ ≤ liminf (fun n => ∫⁻ t in Ici (0:ℝ), f n t) atTop :=
      lintegral_liminf_le hmeas
    _ ≤ C := liminf_le_of_frequently_le'
      (Frequently.of_forall fun n => hbound (lambda n) (hlambdaPos n) (hlambdaOne n))

/-- **The explicit annealed Green bound that the Version 4 chain proves.**
The manuscript's `eq:green-explicit` asserts the same integral is at most
`2048`; the formalized chain reaches `2.75 · 10⁸`. -/
theorem annealed_green_le_numeral :
    (∫⁻ t in Ici (0:ℝ), Manhattan.annealedContinuousKernel t 0 0)
      ≤ ENNReal.ofReal 275000000 := by
  refine undamped_le_of_uniform_damped _ ?_
  intro l hl hl1
  rw [Manhattan.Glue.concreteGreenIdentity l hl]
  exact ENNReal.ofReal_le_ofReal (uniform_green_numeral hl hl1)

end Manhattan.Paper.Constant
