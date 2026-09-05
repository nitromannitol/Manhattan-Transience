import Manhattan.Estimates.Competitor
import Manhattan.Estimates.PropositionFiveTwo
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Three-region frequency integration

This file implements the small-square, square-annulus, and outer-region
estimates in `manuscript.tex:668-681` separately. Their assembly constructs
`Operator.RegionalIntegralBounds` from the actual regional integrals.
-/

noncomputable section

open MeasureTheory Set

namespace Manhattan.Estimates

/-- The square radius `a(p)=max(|p₁|,|p₂|)` in product coordinates. -/
def squareRadius (z : ℝ × ℝ) : ℝ := max |z.1| |z.2|

/-- The normalized product Haar measure on the chosen torus representatives. -/
def torusProductMeasure : Measure (ℝ × ℝ) :=
  (volume.restrict torus).prod (volume.restrict torus)

/-- Normalized integral of a density over a measurable frequency region. -/
def normalizedRegionIntegral (f : ℝ × ℝ → ℝ) (s : Set (ℝ × ℝ)) : ℝ :=
  (2 * Real.pi)⁻¹ ^ 2 * ∫ z in s, f z ∂torusProductMeasure

/-- Full normalized torus integral in product coordinates. -/
def normalizedFrequencyIntegral (f : ℝ × ℝ → ℝ) : ℝ :=
  normalizedRegionIntegral f Set.univ

/-- The small square `a(p) ≤ sqrt λ`. -/
def smallSquare (lambda : ℝ) : Set (ℝ × ℝ) :=
  {z | squareRadius z ≤ Real.sqrt lambda}

/-- The logarithmic square annulus `sqrt λ < a(p) < r₀/2`. -/
def squareAnnulus (r0 lambda : ℝ) : Set (ℝ × ℝ) :=
  {z | Real.sqrt lambda < squareRadius z ∧ squareRadius z < r0 / 2}

/-- The outer region `r₀/2 ≤ a(p)`. -/
def outerRegion (r0 : ℝ) : Set (ℝ × ℝ) :=
  {z | r0 / 2 ≤ squareRadius z}

theorem measurableSet_smallSquare (lambda : ℝ) : MeasurableSet (smallSquare lambda) := by
  have hrad : Measurable squareRadius := by
    unfold squareRadius
    fun_prop
  exact measurableSet_le hrad measurable_const

theorem measurableSet_squareAnnulus (r0 lambda : ℝ) :
    MeasurableSet (squareAnnulus r0 lambda) := by
  have hrad : Measurable squareRadius := by
    unfold squareRadius
    fun_prop
  exact (measurableSet_lt measurable_const hrad).inter
    (measurableSet_lt hrad measurable_const)

theorem measurableSet_outerRegion (r0 : ℝ) : MeasurableSet (outerRegion r0) := by
  have hrad : Measurable squareRadius := by
    unfold squareRadius
    fun_prop
  exact measurableSet_le measurable_const hrad

private theorem torusProductMeasure_lt_top : torusProductMeasure Set.univ < ⊤ := by
  rw [torusProductMeasure, ← Set.univ_prod_univ, Measure.prod_prod]
  have htorus : volume torus < ⊤ := by
    rw [torus]
    exact measure_Ioc_lt_top
  simp only [Measure.restrict_apply_univ]
  exact ENNReal.mul_lt_top htorus htorus

private instance torusProductMeasure_isFinite : IsFiniteMeasure torusProductMeasure :=
  ⟨torusProductMeasure_lt_top⟩

private theorem torusProductMeasure_apply_ne_top (s : Set (ℝ × ℝ)) :
    torusProductMeasure s ≠ ⊤ :=
  ((measure_mono (subset_univ s)).trans_lt torusProductMeasure_lt_top).ne

private theorem ae_mem_torusProduct :
    ∀ᵐ z ∂torusProductMeasure, z.1 ∈ torus ∧ z.2 ∈ torus := by
  rw [torusProductMeasure, Measure.ae_prod_iff_ae_ae]
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    exact ⟨hx, hy⟩
  · exact (measurableSet_Ioc.preimage measurable_fst).inter
      (measurableSet_Ioc.preimage measurable_snd)

private theorem normalizedFactorSq_nonneg : 0 ≤ (2 * Real.pi)⁻¹ ^ 2 := sq_nonneg _

/-- The small square has product measure `4λ` for `0 < λ ≤ 1`. -/
theorem smallSquare_measureReal {lambda : ℝ} (hlambda : 0 < lambda)
    (hlambdaOne : lambda ≤ 1) :
    torusProductMeasure.real (smallSquare lambda) = 4 * lambda := by
  let s : Set ℝ := Set.Icc (-Real.sqrt lambda) (Real.sqrt lambda)
  have hsqrtPos : 0 < Real.sqrt lambda := Real.sqrt_pos.2 hlambda
  have hsqrtOne : Real.sqrt lambda ≤ 1 := Real.sqrt_le_one.mpr hlambdaOne
  have hpi : Real.sqrt lambda < Real.pi :=
    hsqrtOne.trans_lt (by linarith [Real.two_le_pi])
  have hs : smallSquare lambda = s ×ˢ s := by
    ext z
    simp only [smallSquare, squareRadius, Set.mem_setOf_eq, Set.mem_prod, max_le_iff,
      abs_le, s]
    aesop
  have hsMeas : MeasurableSet s := measurableSet_Icc
  have hst : s ⊆ torus := by
    intro x hx
    exact ⟨(neg_lt_neg hpi).trans_le hx.1, hx.2.trans hsqrtOne |>.trans
      (by linarith [Real.two_le_pi])⟩
  have hmeasure : (volume.restrict torus).real s = 2 * Real.sqrt lambda := by
    rw [measureReal_def, Measure.restrict_apply hsMeas, inter_eq_left.mpr hst,
      Real.volume_Icc, ENNReal.toReal_ofReal]
    · ring
    · linarith
  rw [hs, torusProductMeasure, MeasureTheory.measureReal_prod_prod, hmeasure]
  nlinarith [Real.sq_sqrt hlambda.le]

/-- Small-square contribution: the driftless `1/λ` bound cancels the
`O(λ)` area. -/
theorem smallSquare_integral_le {f : ℝ × ℝ → ℝ} {C lambda : ℝ}
    (hC : 0 ≤ C) (hlambda : 0 < lambda) (hlambdaOne : lambda ≤ 1)
    (hf : Measurable f) (hfNonneg : ∀ z, 0 ≤ f z)
    (hpoint : ∀ z ∈ smallSquare lambda, z.1 ∈ torus → z.2 ∈ torus →
      f z ≤ C / lambda) :
    normalizedRegionIntegral f (smallSquare lambda) ≤ C := by
  have hregionInt : IntegrableOn f (smallSquare lambda) torusProductMeasure := by
    apply Integrable.mono'
      (integrableOn_const (torusProductMeasure_apply_ne_top (smallSquare lambda)) :
        Integrable (fun _ : ℝ × ℝ => C / lambda)
          (torusProductMeasure.restrict (smallSquare lambda)))
      hf.aestronglyMeasurable
    have htorus : ∀ᵐ z ∂torusProductMeasure.restrict (smallSquare lambda),
        z.1 ∈ torus ∧ z.2 ∈ torus :=
      ae_mono Measure.restrict_le_self ae_mem_torusProduct
    filter_upwards [ae_restrict_mem (measurableSet_smallSquare lambda), htorus] with z hz hzt
    rw [Real.norm_eq_abs, abs_of_nonneg (hfNonneg z)]
    exact hpoint z hz hzt.1 hzt.2
  rw [normalizedRegionIntegral]
  have hmono : (∫ z in smallSquare lambda, f z ∂torusProductMeasure) ≤
      ∫ _z in smallSquare lambda, C / lambda ∂torusProductMeasure := by
    apply integral_mono_ae hregionInt
      (integrableOn_const (torusProductMeasure_apply_ne_top (smallSquare lambda)))
    have htorus : ∀ᵐ z ∂torusProductMeasure.restrict (smallSquare lambda),
        z.1 ∈ torus ∧ z.2 ∈ torus :=
      ae_mono Measure.restrict_le_self ae_mem_torusProduct
    filter_upwards [ae_restrict_mem (measurableSet_smallSquare lambda), htorus] with z hz hzt
    exact hpoint z hz hzt.1 hzt.2
  calc
    (2 * Real.pi)⁻¹ ^ 2 * (∫ z in smallSquare lambda, f z ∂torusProductMeasure) ≤
        (2 * Real.pi)⁻¹ ^ 2 *
          (∫ _z in smallSquare lambda, C / lambda ∂torusProductMeasure) :=
      mul_le_mul_of_nonneg_left hmono normalizedFactorSq_nonneg
    _ = (2 * Real.pi)⁻¹ ^ 2 *
        (torusProductMeasure.real (smallSquare lambda) * (C / lambda)) := by
      rw [setIntegral_const]
      rfl
    _ = (2 * Real.pi)⁻¹ ^ 2 * (4 * C) := by
      rw [smallSquare_measureReal hlambda hlambdaOne]
      field_simp [hlambda.ne']
    _ ≤ C := by
      have hpiSq : 4 ≤ (2 * Real.pi) ^ 2 := by
        nlinarith [Real.two_le_pi, sq_nonneg (2 * Real.pi - 2)]
      rw [inv_pow]
      calc
        ((2 * Real.pi) ^ 2)⁻¹ * (4 * C) ≤ 1 * C := by
          rw [inv_mul_le_iff₀ (sq_pos_of_pos (mul_pos (by norm_num) Real.pi_pos))]
          nlinarith
        _ = C := one_mul C

/-- On the outer region, the dispersion is uniformly positive. -/
theorem theta_ge_on_outerRegion {r0 : ℝ} (hr0 : 0 < r0) {z : ℝ × ℝ}
    (hz0 : z.1 ∈ torus) (hz1 : z.2 ∈ torus) (hz : z ∈ outerRegion r0) :
    r0 ^ 2 / (2 * Real.pi ^ 2) ≤ Operator.theta ![z.1, z.2] := by
  rw [operator_theta_eq]
  simp only [theta, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hxAbs : |z.1| ≤ Real.pi := abs_le.2 ⟨hz0.1.le, hz0.2⟩
  have hyAbs : |z.2| ≤ Real.pi := abs_le.2 ⟨hz1.1.le, hz1.2⟩
  have hdx := (dispersion_quadratic_bounds hxAbs).1
  have hdy := (dispersion_quadratic_bounds hyAbs).1
  have hmax : r0 / 2 ≤ max |z.1| |z.2| := hz
  rcases max_cases |z.1| |z.2| with hxy | hyx
  · have hx : r0 / 2 ≤ |z.1| := by simpa [hxy] using hmax
    have hsquare : r0 ^ 2 / 4 ≤ z.1 ^ 2 := by
      rw [← sq_abs z.1]
      nlinarith [hr0, abs_nonneg z.1]
    have hpiSq : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
    have : r0 ^ 2 / (2 * Real.pi ^ 2) ≤ 2 * z.1 ^ 2 / Real.pi ^ 2 := by
      rw [div_le_div_iff₀ (mul_pos (by norm_num) hpiSq) hpiSq]
      nlinarith
    exact this.trans (hdx.trans (le_add_of_nonneg_right (dispersion_nonneg z.2)))
  · have hy : r0 / 2 ≤ |z.2| := by simpa [hyx] using hmax
    have hsquare : r0 ^ 2 / 4 ≤ z.2 ^ 2 := by
      rw [← sq_abs z.2]
      nlinarith [hr0, abs_nonneg z.2]
    have hpiSq : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
    have : r0 ^ 2 / (2 * Real.pi ^ 2) ≤ 2 * z.2 ^ 2 / Real.pi ^ 2 := by
      rw [div_le_div_iff₀ (mul_pos (by norm_num) hpiSq) hpiSq]
      nlinarith
    exact this.trans (hdy.trans (le_add_of_nonneg_left (dispersion_nonneg z.1)))

/-- The normalized product Haar measure of the whole torus is one. -/
theorem normalizedRegionIntegral_const_univ (c : ℝ) :
    normalizedRegionIntegral (fun _ : ℝ × ℝ => c) Set.univ = c := by
  rw [normalizedRegionIntegral, setIntegral_univ, integral_const,
    torusProductMeasure, ← Set.univ_prod_univ, MeasureTheory.measureReal_prod_prod]
  simp only [smul_eq_mul]
  have htorus : (volume.restrict torus).real Set.univ = 2 * Real.pi := by
    rw [measureReal_def, Measure.restrict_apply_univ, torus, Real.volume_Ioc,
      ENNReal.toReal_ofReal]
    · ring
    · linarith [Real.pi_pos]
  rw [htorus]
  field_simp [Real.pi_ne_zero]

/-- On the outer region, the first entry of the frequency majorant is bounded
using `theta(p) ≥ r₀²/(2π²)`. -/
theorem frequencyMajorant_le_on_outerRegion {r0 lambda : ℝ}
    (hr0 : 0 < r0) (hlambda : 0 < lambda) {z : ℝ × ℝ}
    (hz0 : z.1 ∈ torus) (hz1 : z.2 ∈ torus) (hz : z ∈ outerRegion r0) :
    Operator.frequencyMajorant r0 lambda ![z.1, z.2] ≤
      2 * Real.pi ^ 2 / r0 ^ 2 := by
  have htheta := theta_ge_on_outerRegion hr0 hz0 hz1 hz
  have hbasePos : 0 < r0 ^ 2 / (2 * Real.pi ^ 2) := by positivity
  have hdenPos : 0 < lambda + Operator.theta ![z.1, z.2] :=
    add_pos_of_pos_of_nonneg hlambda (by rw [operator_theta_eq]; exact theta_nonneg _)
  calc
    Operator.frequencyMajorant r0 lambda ![z.1, z.2] ≤
        Operator.driftlessMajorant lambda ![z.1, z.2] := min_le_left _ _
    _ ≤ (r0 ^ 2 / (2 * Real.pi ^ 2))⁻¹ := by
      unfold Operator.driftlessMajorant
      rw [one_div]
      apply (inv_le_inv₀ hdenPos hbasePos).2
      linarith
    _ = 2 * Real.pi ^ 2 / r0 ^ 2 := by field_simp [hr0.ne', Real.pi_ne_zero]

/-- Outer-region contribution from the torus-restricted frequency bound. -/
theorem outerRegion_integral_le {f : ℝ × ℝ → ℝ} {C r0 lambda : ℝ}
    (hC : 0 ≤ C) (hr0 : 0 < r0) (hlambda : 0 < lambda)
    (hf : Measurable f) (hfNonneg : ∀ z, 0 ≤ f z)
    (hpoint : ∀ z, z.1 ∈ torus → z.2 ∈ torus →
      f z ≤ C * Operator.frequencyMajorant r0 lambda ![z.1, z.2]) :
    normalizedRegionIntegral f (outerRegion r0) ≤
      C * (2 * Real.pi ^ 2 / r0 ^ 2) := by
  let B : ℝ := C * (2 * Real.pi ^ 2 / r0 ^ 2)
  have hBNonneg : 0 ≤ B := by dsimp [B]; positivity
  have hregionInt : IntegrableOn f (outerRegion r0) torusProductMeasure := by
    apply Integrable.mono'
      (integrableOn_const (torusProductMeasure_apply_ne_top (outerRegion r0)) :
        Integrable (fun _ : ℝ × ℝ => B)
          (torusProductMeasure.restrict (outerRegion r0)))
      hf.aestronglyMeasurable
    have htorus : ∀ᵐ z ∂torusProductMeasure.restrict (outerRegion r0),
        z.1 ∈ torus ∧ z.2 ∈ torus :=
      ae_mono Measure.restrict_le_self ae_mem_torusProduct
    filter_upwards [ae_restrict_mem (measurableSet_outerRegion r0), htorus] with z hz hzt
    rw [Real.norm_eq_abs, abs_of_nonneg (hfNonneg z)]
    exact (hpoint z hzt.1 hzt.2).trans
      (mul_le_mul_of_nonneg_left
        (frequencyMajorant_le_on_outerRegion hr0 hlambda hzt.1 hzt.2 hz) hC)
  rw [normalizedRegionIntegral]
  have hmono : (∫ z in outerRegion r0, f z ∂torusProductMeasure) ≤
      ∫ _z in outerRegion r0, B ∂torusProductMeasure := by
    apply integral_mono_ae hregionInt
      (integrableOn_const (torusProductMeasure_apply_ne_top (outerRegion r0)))
    have htorus : ∀ᵐ z ∂torusProductMeasure.restrict (outerRegion r0),
        z.1 ∈ torus ∧ z.2 ∈ torus :=
      ae_mono Measure.restrict_le_self ae_mem_torusProduct
    filter_upwards [ae_restrict_mem (measurableSet_outerRegion r0), htorus] with z hz hzt
    exact (hpoint z hzt.1 hzt.2).trans
      (mul_le_mul_of_nonneg_left
        (frequencyMajorant_le_on_outerRegion hr0 hlambda hzt.1 hzt.2 hz) hC)
  calc
    (2 * Real.pi)⁻¹ ^ 2 * (∫ z in outerRegion r0, f z ∂torusProductMeasure) ≤
        (2 * Real.pi)⁻¹ ^ 2 *
          (∫ _z in outerRegion r0, B ∂torusProductMeasure) :=
      mul_le_mul_of_nonneg_left hmono normalizedFactorSq_nonneg
    _ ≤ (2 * Real.pi)⁻¹ ^ 2 *
        (∫ _z in Set.univ, B ∂torusProductMeasure) := by
      apply mul_le_mul_of_nonneg_left _ normalizedFactorSq_nonneg
      exact setIntegral_mono_set
        (integrableOn_const (torusProductMeasure_apply_ne_top Set.univ))
        (Filter.Eventually.of_forall fun _ => hBNonneg)
        (Filter.Eventually.of_forall fun z _hz => Set.mem_univ z)
    _ = B := normalizedRegionIntegral_const_univ B
    _ = C * (2 * Real.pi ^ 2 / r0 ^ 2) := rfl

/-- The logarithmic factor used after replacing `sqrt λ + a` by `2a`. -/
def annulusLog (r0 x : ℝ) : ℝ := 1 + Real.log (r0 / 2) - Real.log x

/-- The positive half-line density in the square-annulus calculation. -/
noncomputable def annulusLineKernel (r0 x : ℝ) : ℝ :=
  (x * Real.sqrt (annulusLog r0 x) ^ 3)⁻¹

private theorem annulusLog_pos {r0 x : ℝ} (hx : 0 < x) (hxr : x ≤ r0 / 2) :
    0 < annulusLog r0 x := by
  have hrhalf : 0 < r0 / 2 := hx.trans_le hxr
  have hlog := Real.log_le_log hx hxr
  unfold annulusLog
  linarith

private theorem annulusAntiderivative_hasDerivAt {r0 x : ℝ}
    (hx : 0 < x) (hxr : x ≤ r0 / 2) :
    HasDerivAt (fun y : ℝ => 2 * (Real.sqrt (annulusLog r0 y))⁻¹)
      (annulusLineKernel r0 x) x := by
  have hinnerPos := annulusLog_pos hx hxr
  have hinner : HasDerivAt (annulusLog r0) (-1 / x) x := by
    unfold annulusLog
    convert (hasDerivAt_const x (1 + Real.log (r0 / 2))).sub
      (Real.hasDerivAt_log hx.ne') using 1
    ring
  have hsqrt := hinner.sqrt hinnerPos.ne'
  have hinv := hsqrt.inv (Real.sqrt_pos.2 hinnerPos).ne'
  convert hinv.const_mul 2 using 1
  · unfold annulusLineKernel
    field_simp [Real.sqrt_pos.2 hinnerPos |>.ne']

/-- The one-dimensional logarithmic annulus integral is at most two. -/
theorem annulusLineIntegral_le_two {r0 a : ℝ} (ha : 0 < a) (har : a ≤ r0 / 2) :
    (∫ x in a..r0 / 2, annulusLineKernel r0 x) ≤ 2 := by
  have hrhalf : 0 < r0 / 2 := ha.trans_le har
  have hderiv : ∀ x ∈ Set.uIcc a (r0 / 2),
      HasDerivAt (fun y : ℝ => 2 * (Real.sqrt (annulusLog r0 y))⁻¹)
        (annulusLineKernel r0 x) x := by
    intro x hx
    rw [Set.uIcc_of_le har] at hx
    exact annulusAntiderivative_hasDerivAt (ha.trans_le hx.1) hx.2
  have hint : IntervalIntegrable (annulusLineKernel r0) volume a (r0 / 2) := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le har] at hx
    have hxPos := ha.trans_le hx.1
    have hlogPos := annulusLog_pos hxPos hx.2
    apply ContinuousAt.continuousWithinAt
    unfold annulusLineKernel annulusLog
    apply ContinuousAt.inv₀
    · apply ContinuousAt.mul continuousAt_id
      apply ContinuousAt.pow
      apply ContinuousAt.sqrt
      exact continuousAt_const.sub (Real.continuousAt_log hxPos.ne')
    · exact mul_ne_zero hxPos.ne' (pow_ne_zero 3 (Real.sqrt_pos.2 hlogPos).ne')
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have hrightLog : annulusLog r0 (r0 / 2) = 1 := by
    unfold annulusLog
    ring
  rw [hrightLog, Real.sqrt_one, inv_one, mul_one]
  have hleftNonneg : 0 ≤ 2 * (Real.sqrt (annulusLog r0 a))⁻¹ := by positivity
  linarith

/-- The positive half-line annulus density, extended by zero. -/
noncomputable def positiveAnnulusLine (r0 lambda x : ℝ) : ℝ :=
  if Real.sqrt lambda < x ∧ x < r0 / 2 then annulusLineKernel r0 x else 0

/-- Its even extension to the full line. -/
noncomputable def annulusLine (r0 lambda x : ℝ) : ℝ :=
  positiveAnnulusLine r0 lambda |x|

private theorem positiveAnnulusLine_integrable {r0 lambda : ℝ}
    (hlambda : 0 < lambda) :
    Integrable (positiveAnnulusLine r0 lambda) volume := by
  have hsqrtPos := Real.sqrt_pos.2 hlambda
  have hmeas : Measurable (positiveAnnulusLine r0 lambda) := by
    unfold positiveAnnulusLine
    apply Measurable.ite
    · exact (measurableSet_lt measurable_const measurable_id).inter
        (measurableSet_lt measurable_id measurable_const)
    · unfold annulusLineKernel annulusLog
      fun_prop
    · exact measurable_const
  let B : ℝ := (Real.sqrt lambda * 1 ^ 3)⁻¹
  let majorant : ℝ → ℝ := (Set.Ioo 0 (r0 / 2)).indicator fun _ => B
  have hmajorantInt : Integrable majorant volume := by
    have hconst : IntegrableOn (fun _ : ℝ => B) (Set.Ioo 0 (r0 / 2)) :=
      integrableOn_const measure_Ioo_lt_top.ne
    simpa only [majorant] using hconst.integrable_indicator measurableSet_Ioo
  apply Integrable.mono'
    hmajorantInt hmeas.aestronglyMeasurable
  filter_upwards with x
  by_cases hx : Real.sqrt lambda < x ∧ x < r0 / 2
  · have hxPos : 0 < x := hsqrtPos.trans hx.1
    have hlogPos := annulusLog_pos hxPos hx.2.le
    have hxLower : Real.sqrt lambda ≤ x := hx.1.le
    have hrootOne : 1 ≤ Real.sqrt (annulusLog r0 x) := by
      have hlogNonneg : 0 ≤ Real.log (r0 / 2) - Real.log x := by
        exact sub_nonneg.mpr (Real.log_le_log hxPos hx.2.le)
      have hone : 1 ≤ annulusLog r0 x := by
        unfold annulusLog
        linarith
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hone
    have hden : Real.sqrt lambda * 1 ^ 3 ≤
        x * Real.sqrt (annulusLog r0 x) ^ 3 := by
      exact mul_le_mul hxLower (pow_le_pow_left₀ (by norm_num) hrootOne 3)
        (by norm_num) hxPos.le
    have hdenPos : 0 < x * Real.sqrt (annulusLog r0 x) ^ 3 := by positivity
    rw [positiveAnnulusLine, if_pos hx]
    unfold annulusLineKernel
    rw [Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr hdenPos.le)]
    change (x * Real.sqrt (annulusLog r0 x) ^ 3)⁻¹ ≤ majorant x
    rw [show majorant x = B by
      simp [majorant, hsqrtPos.trans hx.1, hx.2]]
    exact (inv_le_inv₀ hdenPos (by positivity)).2 hden
  · rw [positiveAnnulusLine, if_neg hx, norm_zero]
    exact (Set.indicator_nonneg fun _ _ => inv_nonneg.mpr
      (mul_nonneg (Real.sqrt_nonneg _) (by norm_num))) x

/-- The one-dimensional even annulus integral is uniformly bounded. -/
theorem annulusLine_torusIntegral_le_four {r0 lambda : ℝ}
    (hr0 : 0 < r0) (hr0One : r0 < 1) (hlambda : 0 < lambda) :
    torusIntegral (annulusLine r0 lambda) ≤ 4 := by
  have hsqrtPos := Real.sqrt_pos.2 hlambda
  have hRpi : r0 / 2 < Real.pi := by linarith [Real.two_le_pi]
  by_cases har : Real.sqrt lambda ≤ r0 / 2
  swap
  · have hzero : annulusLine r0 lambda = fun _ => 0 := by
      funext x
      simp only [annulusLine, positiveAnnulusLine]
      rw [if_neg]
      intro hx
      exact har (hx.1.le.trans hx.2.le)
    rw [hzero]
    simp [torusIntegral]
  have hsupport : ∀ x : ℝ, x ∉ torus → annulusLine r0 lambda x = 0 := by
    intro x hxTorus
    unfold annulusLine positiveAnnulusLine
    split_ifs with hx
    · exfalso
      apply hxTorus
      have habsPi : |x| < Real.pi := hx.2.trans hRpi
      exact ⟨(neg_lt_neg habsPi).trans_le (neg_abs_le x),
        ((le_abs_self x).trans_lt habsPi).le⟩
    · rfl
  have hrestricted : (∫ x in torus, annulusLine r0 lambda x) =
      ∫ x, annulusLine r0 lambda x := by
    calc
      (∫ x in torus, annulusLine r0 lambda x) =
          ∫ x, torus.indicator (annulusLine r0 lambda) x :=
        (integral_indicator measurableSet_Ioc).symm
      _ = ∫ x, annulusLine r0 lambda x := by
        apply integral_congr_ae
        filter_upwards with x
        by_cases hx : x ∈ torus
        · simp [hx]
        · simp [hx, hsupport x hx]
  have hpositive : (∫ x in Set.Ioi 0, positiveAnnulusLine r0 lambda x) =
      ∫ x in Set.Ioo (Real.sqrt lambda) (r0 / 2), annulusLineKernel r0 x := by
    rw [show positiveAnnulusLine r0 lambda =
        (Set.Ioo (Real.sqrt lambda) (r0 / 2)).indicator (annulusLineKernel r0) by
      funext x
      by_cases hx : Real.sqrt lambda < x ∧ x < r0 / 2
      · rw [positiveAnnulusLine, if_pos hx]
        have hxmem : x ∈ Set.Ioo (Real.sqrt lambda) (r0 / 2) := hx
        rw [Set.indicator_of_mem hxmem]
      · rw [positiveAnnulusLine, if_neg hx]
        have hxmem : x ∉ Set.Ioo (Real.sqrt lambda) (r0 / 2) := hx
        rw [Set.indicator_of_notMem hxmem]]
    rw [integral_indicator measurableSet_Ioo,
      Measure.restrict_restrict measurableSet_Ioo]
    have hinter : Set.Ioo (Real.sqrt lambda) (r0 / 2) ∩ Set.Ioi 0 =
        Set.Ioo (Real.sqrt lambda) (r0 / 2) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_Ioi]
      constructor
      · exact fun hx => hx.1
      · intro hx
        exact ⟨hx, (Real.sqrt_pos.2 hlambda).trans hx.1⟩
    rw [hinter]
  rw [torusIntegral, hrestricted]
  simp only [smul_eq_mul]
  unfold annulusLine
  rw [integral_comp_abs, hpositive,
    ← integral_Icc_eq_integral_Ioo,
    integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le har]
  have hline := annulusLineIntegral_le_two hsqrtPos har
  calc
    (2 * Real.pi)⁻¹ * (2 * ∫ x in Real.sqrt lambda..r0 / 2,
        annulusLineKernel r0 x) ≤
        (2 * Real.pi)⁻¹ * (2 * 2) := by gcongr
    _ ≤ 4 := by
      have hpiInv : (2 * Real.pi)⁻¹ ≤ 1 :=
        (inv_le_one₀ (by positivity)).2 (by linarith [Real.two_le_pi])
      nlinarith

/-- The wedge majorant on which the first coordinate realizes the square
radius. -/
noncomputable def annulusWedgeX (r0 lambda : ℝ) (z : ℝ × ℝ) : ℝ :=
  if Real.sqrt lambda < |z.1| ∧ |z.1| < r0 / 2 then
    (((z.1 ^ 2 + z.2 ^ 2) / 2) * Real.sqrt (annulusLog r0 |z.1|) ^ 3)⁻¹
  else 0

/-- The symmetric wedge majorant on which the second coordinate realizes
the square radius. -/
noncomputable def annulusWedgeY (r0 lambda : ℝ) (z : ℝ × ℝ) : ℝ :=
  annulusWedgeX r0 lambda (z.2, z.1)

private theorem frequencyLogScale_ge_annulusLog {r0 lambda a : ℝ}
    {p : Fin 2 → ℝ} (hmax : Operator.maxFrequency p = a)
    (hr0 : 0 < r0) (hlambda : 0 < lambda) (ha : Real.sqrt lambda < a)
    (_har : a < r0 / 2) :
    annulusLog r0 a ≤ Operator.frequencyLogScale r0 lambda p := by
  have haPos : 0 < a := (Real.sqrt_pos.2 hlambda).trans ha
  have hsumPos : 0 < Real.sqrt lambda + a :=
    add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) haPos
  have htwoa : Real.sqrt lambda + a < 2 * a := by linarith
  have hratioLe : r0 / (2 * a) ≤ r0 / (Real.sqrt lambda + a) :=
    div_le_div_of_nonneg_left hr0.le hsumPos htwoa.le
  have hlogLe := Real.log_le_log (div_pos hr0 (mul_pos (by norm_num) haPos)) hratioLe
  have hrawLe : annulusLog r0 a ≤
      1 + Real.log (r0 / (Real.sqrt lambda + a)) := by
    have hrhalf : 0 < r0 / 2 := by positivity
    have hlogIdentity : annulusLog r0 a = 1 + Real.log (r0 / (2 * a)) := by
      unfold annulusLog
      rw [Real.log_div hr0.ne' (mul_pos (by norm_num) haPos).ne',
        Real.log_div hr0.ne' (by positivity : (2 : ℝ) ≠ 0),
        Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) haPos.ne']
      ring
    rw [hlogIdentity]
    linarith
  calc
    annulusLog r0 a ≤ 1 + Real.log (r0 / (Real.sqrt lambda + a)) := hrawLe
    _ ≤ 1 + Operator.logPos (r0 / (Real.sqrt lambda + a)) := by
      unfold Operator.logPos
      gcongr
      exact le_max_left _ _
    _ = Operator.frequencyLogScale r0 lambda p := by
      rw [Operator.frequencyLogScale, hmax]

private theorem frequencyMajorant_le_annulusEnvelope {r0 lambda : ℝ}
    (hr0 : 0 < r0) (hlambda : 0 < lambda) {z : ℝ × ℝ}
    (hz : z ∈ squareAnnulus r0 lambda) :
    Operator.frequencyMajorant r0 lambda ![z.1, z.2] ≤
      (squareRadius z ^ 2 * Real.sqrt (annulusLog r0 (squareRadius z)) ^ 3)⁻¹ := by
  let a := squareRadius z
  have haLower : Real.sqrt lambda < a := hz.1
  have haUpper : a < r0 / 2 := hz.2
  have haPos : 0 < a := (Real.sqrt_pos.2 hlambda).trans haLower
  have hlogPos : 0 < annulusLog r0 a := annulusLog_pos haPos haUpper.le
  have hfreqLog : annulusLog r0 a ≤
      Operator.frequencyLogScale r0 lambda ![z.1, z.2] := by
    have hmax : Operator.maxFrequency ![z.1, z.2] = a := by
      simp [Operator.maxFrequency, a, squareRadius]
    exact frequencyLogScale_ge_annulusLog hmax hr0 hlambda haLower haUpper
  have hfreqPos : 0 < Operator.frequencyLogScale r0 lambda ![z.1, z.2] := by
    rw [Operator.frequencyLogScale]
    exact add_pos_of_pos_of_nonneg zero_lt_one (le_max_right _ _)
  have hpow : annulusLog r0 a ^ (3 / 2 : ℝ) ≤
      Operator.frequencyLogScale r0 lambda ![z.1, z.2] ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow hlogPos.le hfreqLog (by norm_num)
  have hpowSqrt : annulusLog r0 a ^ (3 / 2 : ℝ) =
      Real.sqrt (annulusLog r0 a) ^ 3 := by
    calc
      annulusLog r0 a ^ (3 / 2 : ℝ) =
          Real.sqrt (annulusLog r0 a) ^ (3 : ℝ) :=
        Real.rpow_div_two_eq_sqrt 3 hlogPos.le
      _ = Real.sqrt (annulusLog r0 a) ^ (3 : ℕ) :=
        Real.rpow_natCast _ 3
  have hfreqPowPos : 0 <
      Operator.frequencyLogScale r0 lambda ![z.1, z.2] ^ (3 / 2 : ℝ) :=
    Real.rpow_pos_of_pos hfreqPos _
  have hdenLe : a ^ 2 * annulusLog r0 a ^ (3 / 2 : ℝ) ≤
      a ^ 2 * Operator.frequencyLogScale r0 lambda ![z.1, z.2] ^ (3 / 2 : ℝ) :=
    mul_le_mul_of_nonneg_left hpow (sq_nonneg _)
  have hleftPos : 0 < a ^ 2 * annulusLog r0 a ^ (3 / 2 : ℝ) := by positivity
  have hrightPos : 0 < a ^ 2 *
      Operator.frequencyLogScale r0 lambda ![z.1, z.2] ^ (3 / 2 : ℝ) := by positivity
  have hmax : Operator.maxFrequency ![z.1, z.2] = a := by
    simp [Operator.maxFrequency, a, squareRadius]
  have hmaxNe : Operator.maxFrequency ![z.1, z.2] ≠ 0 := by
    intro hzero
    exact haPos.ne' (hmax.symm.trans hzero)
  calc
    Operator.frequencyMajorant r0 lambda ![z.1, z.2] ≤
        Operator.correctedMajorant r0 lambda ![z.1, z.2] := min_le_right _ _
    _ = (a ^ 2 *
        Operator.frequencyLogScale r0 lambda ![z.1, z.2] ^ (3 / 2 : ℝ))⁻¹ := by
      rw [Operator.correctedMajorant, if_neg hmaxNe, one_div]
      rw [hmax]
    _ ≤ (a ^ 2 * annulusLog r0 a ^ (3 / 2 : ℝ))⁻¹ :=
      (inv_le_inv₀ hrightPos hleftPos).2 hdenLe
    _ = (squareRadius z ^ 2 *
        Real.sqrt (annulusLog r0 (squareRadius z)) ^ 3)⁻¹ := by
      rw [hpowSqrt]

/-- On the square annulus, the corrected frequency majorant is bounded by
the sum of the two square-coordinate wedges. -/
theorem frequencyMajorant_le_annulusWedges {r0 lambda : ℝ}
    (hr0 : 0 < r0) (hlambda : 0 < lambda) {z : ℝ × ℝ}
    (hz : z ∈ squareAnnulus r0 lambda) :
    Operator.frequencyMajorant r0 lambda ![z.1, z.2] ≤
      annulusWedgeX r0 lambda z + annulusWedgeY r0 lambda z := by
  have hbase := frequencyMajorant_le_annulusEnvelope hr0 hlambda hz
  rcases max_cases |z.1| |z.2| with hxy | hyx
  · have hyLe : |z.2| ≤ |z.1| := by
      exact hxy.2
    have hxPos : 0 < |z.1| := by
      have : 0 < squareRadius z := (Real.sqrt_pos.2 hlambda).trans hz.1
      simpa [squareRadius, hxy.1] using this
    have hxRegion : Real.sqrt lambda < |z.1| ∧ |z.1| < r0 / 2 := by
      exact ⟨by simpa [squareRadius, hxy.1] using hz.1,
        by simpa [squareRadius, hxy.1] using hz.2⟩
    have hsumPos : 0 < (z.1 ^ 2 + z.2 ^ 2) / 2 := by
      rw [← sq_abs z.1, ← sq_abs z.2]
      positivity
    have hrootPos : 0 < Real.sqrt (annulusLog r0 |z.1|) ^ 3 := by
      have := annulusLog_pos hxPos hxRegion.2.le
      positivity
    have hdenLe : ((z.1 ^ 2 + z.2 ^ 2) / 2) *
        Real.sqrt (annulusLog r0 |z.1|) ^ 3 ≤
        |z.1| ^ 2 * Real.sqrt (annulusLog r0 |z.1|) ^ 3 := by
      apply mul_le_mul_of_nonneg_right _ hrootPos.le
      rw [← sq_abs z.1, ← sq_abs z.2]
      nlinarith [sq_nonneg (|z.1| - |z.2|), abs_nonneg z.1, abs_nonneg z.2]
    have hwedge : (|z.1| ^ 2 * Real.sqrt (annulusLog r0 |z.1|) ^ 3)⁻¹ ≤
        annulusWedgeX r0 lambda z := by
      rw [annulusWedgeX, if_pos hxRegion]
      exact (inv_le_inv₀ (mul_pos (sq_pos_of_pos hxPos) hrootPos)
        (mul_pos hsumPos hrootPos)).2 hdenLe
    calc
      Operator.frequencyMajorant r0 lambda ![z.1, z.2] ≤
          (|z.1| ^ 2 * Real.sqrt (annulusLog r0 |z.1|) ^ 3)⁻¹ := by
        simpa [squareRadius, hxy.1] using hbase
      _ ≤ annulusWedgeX r0 lambda z := hwedge
      _ ≤ annulusWedgeX r0 lambda z + annulusWedgeY r0 lambda z :=
        le_add_of_nonneg_right (by unfold annulusWedgeY annulusWedgeX; split_ifs <;> positivity)
  · have hxLe : |z.1| ≤ |z.2| := by
      exact hyx.2.le
    have hyPos : 0 < |z.2| := by
      have : 0 < squareRadius z := (Real.sqrt_pos.2 hlambda).trans hz.1
      simpa [squareRadius, hyx.1] using this
    have hyRegion : Real.sqrt lambda < |z.2| ∧ |z.2| < r0 / 2 := by
      exact ⟨by simpa [squareRadius, hyx.1] using hz.1,
        by simpa [squareRadius, hyx.1] using hz.2⟩
    have hsumPos : 0 < (z.2 ^ 2 + z.1 ^ 2) / 2 := by
      rw [← sq_abs z.2, ← sq_abs z.1]
      positivity
    have hrootPos : 0 < Real.sqrt (annulusLog r0 |z.2|) ^ 3 := by
      have := annulusLog_pos hyPos hyRegion.2.le
      positivity
    have hdenLe : ((z.2 ^ 2 + z.1 ^ 2) / 2) *
        Real.sqrt (annulusLog r0 |z.2|) ^ 3 ≤
        |z.2| ^ 2 * Real.sqrt (annulusLog r0 |z.2|) ^ 3 := by
      apply mul_le_mul_of_nonneg_right _ hrootPos.le
      rw [← sq_abs z.2, ← sq_abs z.1]
      nlinarith [sq_nonneg (|z.2| - |z.1|), abs_nonneg z.1, abs_nonneg z.2]
    have hwedge : (|z.2| ^ 2 * Real.sqrt (annulusLog r0 |z.2|) ^ 3)⁻¹ ≤
        annulusWedgeY r0 lambda z := by
      unfold annulusWedgeY
      rw [annulusWedgeX, if_pos hyRegion]
      exact (inv_le_inv₀ (mul_pos (sq_pos_of_pos hyPos) hrootPos)
        (mul_pos hsumPos hrootPos)).2 hdenLe
    calc
      Operator.frequencyMajorant r0 lambda ![z.1, z.2] ≤
          (|z.2| ^ 2 * Real.sqrt (annulusLog r0 |z.2|) ^ 3)⁻¹ := by
        simpa [squareRadius, hyx.1] using hbase
      _ ≤ annulusWedgeY r0 lambda z := hwedge
      _ ≤ annulusWedgeX r0 lambda z + annulusWedgeY r0 lambda z :=
        le_add_of_nonneg_left (by unfold annulusWedgeX; split_ifs <;> positivity)

theorem annulusWedgeX_measurable (r0 lambda : ℝ) :
    Measurable (annulusWedgeX r0 lambda) := by
  have habsFst : Measurable (fun z : ℝ × ℝ => |z.1|) := by fun_prop
  unfold annulusWedgeX
  apply Measurable.ite
  · exact (measurableSet_lt measurable_const habsFst).inter
      (measurableSet_lt habsFst measurable_const)
  · unfold annulusLog
    fun_prop
  · exact measurable_const

theorem annulusWedgeY_measurable (r0 lambda : ℝ) :
    Measurable (annulusWedgeY r0 lambda) := by
  unfold annulusWedgeY
  apply (annulusWedgeX_measurable r0 lambda).comp
  fun_prop

theorem annulusWedgeX_nonneg (r0 lambda : ℝ) (z : ℝ × ℝ) :
    0 ≤ annulusWedgeX r0 lambda z := by
  unfold annulusWedgeX
  split_ifs
  · positivity
  · exact le_rfl

theorem annulusWedgeY_nonneg (r0 lambda : ℝ) (z : ℝ × ℝ) :
    0 ≤ annulusWedgeY r0 lambda z :=
  annulusWedgeX_nonneg r0 lambda (z.2, z.1)

private theorem annulusWedgeX_le {r0 lambda : ℝ} (hlambda : 0 < lambda)
    (z : ℝ × ℝ) : annulusWedgeX r0 lambda z ≤ 2 / lambda := by
  by_cases hz : Real.sqrt lambda < |z.1| ∧ |z.1| < r0 / 2
  swap
  · rw [annulusWedgeX, if_neg hz]
    positivity
  have hxPos : 0 < |z.1| := (Real.sqrt_pos.2 hlambda).trans hz.1
  have hxSq : lambda < z.1 ^ 2 := by
    rw [← sq_abs]
    nlinarith [Real.sq_sqrt hlambda.le,
      sq_nonneg (|z.1| - Real.sqrt lambda), Real.sqrt_nonneg lambda]
  have hlogOne : 1 ≤ annulusLog r0 |z.1| := by
    have hlogNonneg : 0 ≤ Real.log (r0 / 2) - Real.log |z.1| :=
      sub_nonneg.mpr (Real.log_le_log hxPos hz.2.le)
    unfold annulusLog
    linarith
  have hrootOne : 1 ≤ Real.sqrt (annulusLog r0 |z.1|) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hlogOne
  have hsumLower : lambda / 2 ≤ (z.1 ^ 2 + z.2 ^ 2) / 2 := by
    nlinarith [sq_nonneg z.2]
  have hdenLower : lambda / 2 ≤
      ((z.1 ^ 2 + z.2 ^ 2) / 2) * Real.sqrt (annulusLog r0 |z.1|) ^ 3 := by
    calc
      lambda / 2 ≤ (z.1 ^ 2 + z.2 ^ 2) / 2 := hsumLower
      _ ≤ ((z.1 ^ 2 + z.2 ^ 2) / 2) *
          Real.sqrt (annulusLog r0 |z.1|) ^ 3 := by
        have hsumNonneg : 0 ≤ (z.1 ^ 2 + z.2 ^ 2) / 2 := by positivity
        nlinarith [pow_le_pow_left₀ (by norm_num : 0 ≤ (1 : ℝ)) hrootOne 3]
  have hdenPos : 0 < ((z.1 ^ 2 + z.2 ^ 2) / 2) *
      Real.sqrt (annulusLog r0 |z.1|) ^ 3 :=
    (div_pos hlambda (by norm_num)).trans_le hdenLower
  rw [annulusWedgeX, if_pos hz]
  calc
    (((z.1 ^ 2 + z.2 ^ 2) / 2) *
        Real.sqrt (annulusLog r0 |z.1|) ^ 3)⁻¹ ≤ (lambda / 2)⁻¹ :=
      (inv_le_inv₀ hdenPos (div_pos hlambda (by norm_num))).2 hdenLower
    _ = 2 / lambda := by field_simp [hlambda.ne']

private theorem annulusWedgeY_le {r0 lambda : ℝ} (hlambda : 0 < lambda)
    (z : ℝ × ℝ) : annulusWedgeY r0 lambda z ≤ 2 / lambda := by
  exact annulusWedgeX_le hlambda (z.2, z.1)

theorem annulusWedgeX_integrable {r0 lambda : ℝ} (hlambda : 0 < lambda) :
    Integrable (annulusWedgeX r0 lambda) torusProductMeasure := by
  have hconst : Integrable (fun _ : ℝ × ℝ => 2 / lambda) torusProductMeasure := by
    exact integrable_const _
  apply Integrable.mono' hconst (annulusWedgeX_measurable r0 lambda).aestronglyMeasurable
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_nonneg (annulusWedgeX_nonneg r0 lambda z)]
  exact annulusWedgeX_le hlambda z

theorem annulusWedgeY_integrable {r0 lambda : ℝ} (hlambda : 0 < lambda) :
    Integrable (annulusWedgeY r0 lambda) torusProductMeasure := by
  have hconst : Integrable (fun _ : ℝ × ℝ => 2 / lambda) torusProductMeasure := by
    exact integrable_const _
  apply Integrable.mono' hconst (annulusWedgeY_measurable r0 lambda).aestronglyMeasurable
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_nonneg (annulusWedgeY_nonneg r0 lambda z)]
  exact annulusWedgeY_le hlambda z

private theorem regional_torusIntegral_const_mul (c : ℝ) (f : ℝ → ℝ) :
    torusIntegral (fun x => c * f x) = c * torusIntegral f := by
  simp only [torusIntegral, integral_const_mul, smul_eq_mul]
  ring

private theorem annulusWedgeX_torusIntegral_le {r0 lambda x : ℝ}
    (hlambda : 0 < lambda) :
    torusIntegral (fun y => annulusWedgeX r0 lambda (x, y)) ≤
      2 * annulusLine r0 lambda x := by
  by_cases hx : Real.sqrt lambda < |x| ∧ |x| < r0 / 2
  swap
  · have hzero : (fun y => annulusWedgeX r0 lambda (x, y)) = fun _ => 0 := by
      funext y
      rw [annulusWedgeX, if_neg hx]
    rw [hzero]
    simp [torusIntegral, annulusLine, positiveAnnulusLine, hx]
  have hxPos : 0 < |x| := (Real.sqrt_pos.2 hlambda).trans hx.1
  have hlogPos : 0 < annulusLog r0 |x| := annulusLog_pos hxPos hx.2.le
  let c : ℝ := 2 * (Real.sqrt (annulusLog r0 |x|) ^ 3)⁻¹
  have hfun : (fun y => annulusWedgeX r0 lambda (x, y)) =
      fun y => c * (|x| ^ 2 + 1 ^ 2 * y ^ 2)⁻¹ := by
    funext y
    rw [annulusWedgeX, if_pos hx]
    dsimp [c]
    rw [one_pow, one_mul, sq_abs]
    field_simp [Real.sqrt_pos.2 hlogPos |>.ne']
  rw [hfun, regional_torusIntegral_const_mul]
  have hcauchy := torusIntegral_cauchy_le hxPos (by norm_num : (0 : ℝ) < 1)
  calc
    c * torusIntegral (fun y : ℝ => (|x| ^ 2 + 1 ^ 2 * y ^ 2)⁻¹) ≤
        c * (1 / (|x| * 1)) := by
      exact mul_le_mul_of_nonneg_left hcauchy (by dsimp [c]; positivity)
    _ = 2 * annulusLine r0 lambda x := by
      rw [annulusLine, positiveAnnulusLine, if_pos hx]
      unfold annulusLineKernel
      dsimp [c]
      field_simp [hxPos.ne', Real.sqrt_pos.2 hlogPos |>.ne']

private theorem annulusLine_measurable (r0 lambda : ℝ) :
    Measurable (annulusLine r0 lambda) := by
  unfold annulusLine positiveAnnulusLine
  apply Measurable.ite
  · have habs : Measurable fun x : ℝ => |x| := by fun_prop
    exact (measurableSet_lt measurable_const habs).inter
      (measurableSet_lt habs measurable_const)
  · unfold annulusLineKernel annulusLog
    fun_prop
  · exact measurable_const

private theorem annulusLine_le {r0 lambda : ℝ} (hlambda : 0 < lambda)
    (x : ℝ) : annulusLine r0 lambda x ≤ (Real.sqrt lambda)⁻¹ := by
  by_cases hx : Real.sqrt lambda < |x| ∧ |x| < r0 / 2
  swap
  · simp [annulusLine, positiveAnnulusLine, hx]
  have hxPos : 0 < |x| := (Real.sqrt_pos.2 hlambda).trans hx.1
  have hlogOne : 1 ≤ annulusLog r0 |x| := by
    have hlogNonneg : 0 ≤ Real.log (r0 / 2) - Real.log |x| :=
      sub_nonneg.mpr (Real.log_le_log hxPos hx.2.le)
    unfold annulusLog
    linarith
  have hrootOne : 1 ≤ Real.sqrt (annulusLog r0 |x|) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hlogOne
  have hdenLower : Real.sqrt lambda ≤
      |x| * Real.sqrt (annulusLog r0 |x|) ^ 3 := by
    calc
      Real.sqrt lambda ≤ |x| := hx.1.le
      _ ≤ |x| * Real.sqrt (annulusLog r0 |x|) ^ 3 := by
        have hxNonneg := abs_nonneg x
        nlinarith [pow_le_pow_left₀ (by norm_num : 0 ≤ (1 : ℝ)) hrootOne 3]
  have hdenPos : 0 < |x| * Real.sqrt (annulusLog r0 |x|) ^ 3 :=
    (Real.sqrt_pos.2 hlambda).trans_le hdenLower
  rw [annulusLine, positiveAnnulusLine, if_pos hx]
  unfold annulusLineKernel
  exact (inv_le_inv₀ hdenPos (Real.sqrt_pos.2 hlambda)).2 hdenLower

private theorem annulusLine_integrable_torus {r0 lambda : ℝ}
    (hlambda : 0 < lambda) :
    Integrable (annulusLine r0 lambda) (volume.restrict torus) := by
  apply Integrable.mono'
    (integrableOn_const measure_Ioc_lt_top.ne :
      Integrable (fun _ : ℝ => (Real.sqrt lambda)⁻¹) (volume.restrict torus))
    (annulusLine_measurable r0 lambda).aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · exact annulusLine_le hlambda x
  · unfold annulusLine positiveAnnulusLine annulusLineKernel
    split_ifs <;> positivity

private theorem normalizedFrequencyIntegral_eq_iterated {f : ℝ × ℝ → ℝ}
    (hf : Integrable f torusProductMeasure) :
    normalizedFrequencyIntegral f =
      torusIntegral (fun x => torusIntegral (fun y => f (x, y))) := by
  rw [normalizedFrequencyIntegral, normalizedRegionIntegral, setIntegral_univ,
    torusProductMeasure]
  change Integrable f ((volume.restrict torus).prod (volume.restrict torus)) at hf
  have hf' : Integrable (Function.uncurry fun x y => f (x, y))
      ((volume.restrict torus).prod (volume.restrict torus)) := by
    simpa [Function.uncurry] using hf
  rw [← MeasureTheory.integral_integral hf']
  simp only [torusIntegral, integral_const_mul, smul_eq_mul]
  ring

/-- The first square-annulus wedge has a uniform normalized integral. -/
theorem normalizedFrequencyIntegral_annulusWedgeX_le_eight {r0 lambda : ℝ}
    (hr0 : 0 < r0) (hr0One : r0 < 1) (hlambda : 0 < lambda) :
    normalizedFrequencyIntegral (annulusWedgeX r0 lambda) ≤ 8 := by
  have hWedgeInt := annulusWedgeX_integrable (r0 := r0) hlambda
  rw [normalizedFrequencyIntegral_eq_iterated hWedgeInt]
  have hWedgeProdInt : Integrable (annulusWedgeX r0 lambda)
      ((volume.restrict torus).prod (volume.restrict torus)) := by
    simpa only [torusProductMeasure] using hWedgeInt
  have hinnerInt := hWedgeProdInt.integral_prod_left
  have hinnerTorusInt : Integrable (fun x =>
      torusIntegral (fun y => annulusWedgeX r0 lambda (x, y)))
      (volume.restrict torus) := by
    simp only [torusIntegral]
    exact hinnerInt.const_mul _
  have hlineInt := annulusLine_integrable_torus (r0 := r0) hlambda
  have hmono : torusIntegral (fun x =>
      torusIntegral (fun y => annulusWedgeX r0 lambda (x, y))) ≤
      torusIntegral (fun x => 2 * annulusLine r0 lambda x) := by
    rw [torusIntegral, torusIntegral]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (by positivity))
    apply integral_mono hinnerTorusInt (hlineInt.const_mul 2)
    intro x
    exact annulusWedgeX_torusIntegral_le hlambda
  calc
    torusIntegral (fun x => torusIntegral (fun y =>
        annulusWedgeX r0 lambda (x, y))) ≤
        torusIntegral (fun x => 2 * annulusLine r0 lambda x) := hmono
    _ = 2 * torusIntegral (annulusLine r0 lambda) :=
      regional_torusIntegral_const_mul 2 _
    _ ≤ 8 := by
      nlinarith [annulusLine_torusIntegral_le_four hr0 hr0One hlambda]

/-- The second square-annulus wedge obeys the same uniform bound by product
measure symmetry. -/
theorem normalizedFrequencyIntegral_annulusWedgeY_le_eight {r0 lambda : ℝ}
    (hr0 : 0 < r0) (hr0One : r0 < 1) (hlambda : 0 < lambda) :
    normalizedFrequencyIntegral (annulusWedgeY r0 lambda) ≤ 8 := by
  have hswap : normalizedFrequencyIntegral (annulusWedgeY r0 lambda) =
      normalizedFrequencyIntegral (annulusWedgeX r0 lambda) := by
    unfold normalizedFrequencyIntegral normalizedRegionIntegral
    rw [setIntegral_univ, setIntegral_univ, torusProductMeasure]
    congr 1
    simpa [annulusWedgeY, Prod.swap] using
      (MeasureTheory.integral_prod_swap
        (μ := volume.restrict torus) (ν := volume.restrict torus)
        (annulusWedgeX r0 lambda))
  rw [hswap]
  exact normalizedFrequencyIntegral_annulusWedgeX_le_eight hr0 hr0One hlambda

/-- The small-square estimate specialized to the torus frequency majorant. -/
theorem smallSquare_frequency_integral_le {f : ℝ × ℝ → ℝ}
    {C r0 lambda : ℝ} (hC : 0 ≤ C) (hlambda : 0 < lambda)
    (hlambdaOne : lambda ≤ 1) (hf : Measurable f)
    (hfNonneg : ∀ z, 0 ≤ f z)
    (hpoint : ∀ z, z.1 ∈ torus → z.2 ∈ torus →
      f z ≤ C * Operator.frequencyMajorant r0 lambda ![z.1, z.2]) :
    normalizedRegionIntegral f (smallSquare lambda) ≤ C := by
  apply smallSquare_integral_le hC hlambda hlambdaOne hf hfNonneg
  intro z hz hz0 hz1
  have hthetaNonneg : 0 ≤ Operator.theta ![z.1, z.2] := by
    rw [operator_theta_eq]
    exact theta_nonneg _
  have hdenPos : 0 < lambda + Operator.theta ![z.1, z.2] :=
    add_pos_of_pos_of_nonneg hlambda hthetaNonneg
  calc
    f z ≤ C * Operator.frequencyMajorant r0 lambda ![z.1, z.2] :=
      hpoint z hz0 hz1
    _ ≤ C * Operator.driftlessMajorant lambda ![z.1, z.2] :=
      mul_le_mul_of_nonneg_left (min_le_left _ _) hC
    _ ≤ C * (1 / lambda) := by
      apply mul_le_mul_of_nonneg_left _ hC
      unfold Operator.driftlessMajorant
      rw [one_div, one_div]
      exact (inv_le_inv₀ hdenPos hlambda).2 (le_add_of_nonneg_right hthetaNonneg)
    _ = C / lambda := by ring

/-- The square-annulus contribution, proved from the two integrable wedge
majorants rather than assumed as aggregate regional data. -/
theorem squareAnnulus_integral_le {f : ℝ × ℝ → ℝ}
    {C r0 lambda : ℝ} (hC : 0 ≤ C) (hr0 : 0 < r0)
    (hr0One : r0 < 1) (hlambda : 0 < lambda) (hf : Measurable f)
    (hfNonneg : ∀ z, 0 ≤ f z)
    (hpoint : ∀ z, z.1 ∈ torus → z.2 ∈ torus →
      f z ≤ C * Operator.frequencyMajorant r0 lambda ![z.1, z.2]) :
    normalizedRegionIntegral f (squareAnnulus r0 lambda) ≤ 16 * C := by
  let W : ℝ × ℝ → ℝ := fun z => C *
    (annulusWedgeX r0 lambda z + annulusWedgeY r0 lambda z)
  have hXInt := annulusWedgeX_integrable (r0 := r0) hlambda
  have hYInt := annulusWedgeY_integrable (r0 := r0) hlambda
  have hWInt : Integrable W torusProductMeasure := by
    exact (hXInt.add hYInt).const_mul C
  have hWNonneg : ∀ z, 0 ≤ W z := by
    intro z
    dsimp [W]
    exact mul_nonneg hC (add_nonneg
      (annulusWedgeX_nonneg r0 lambda z) (annulusWedgeY_nonneg r0 lambda z))
  have hregionInt : IntegrableOn f (squareAnnulus r0 lambda)
      torusProductMeasure := by
    apply Integrable.mono' (hWInt.mono_measure Measure.restrict_le_self)
      hf.aestronglyMeasurable
    have htorus : ∀ᵐ z ∂torusProductMeasure.restrict (squareAnnulus r0 lambda),
        z.1 ∈ torus ∧ z.2 ∈ torus :=
      ae_mono Measure.restrict_le_self ae_mem_torusProduct
    filter_upwards [ae_restrict_mem (measurableSet_squareAnnulus r0 lambda), htorus]
      with z hz hzt
    have hle := (hpoint z hzt.1 hzt.2).trans
      (mul_le_mul_of_nonneg_left
        (frequencyMajorant_le_annulusWedges hr0 hlambda hz) hC)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hfNonneg z),
      abs_of_nonneg (hWNonneg z)] using hle
  have hregionMono : (∫ z in squareAnnulus r0 lambda, f z ∂torusProductMeasure) ≤
      ∫ z in squareAnnulus r0 lambda, W z ∂torusProductMeasure := by
    apply integral_mono_ae hregionInt (hWInt.mono_measure Measure.restrict_le_self)
    have htorus : ∀ᵐ z ∂torusProductMeasure.restrict (squareAnnulus r0 lambda),
        z.1 ∈ torus ∧ z.2 ∈ torus :=
      ae_mono Measure.restrict_le_self ae_mem_torusProduct
    filter_upwards [ae_restrict_mem (measurableSet_squareAnnulus r0 lambda), htorus]
      with z hz hzt
    exact (hpoint z hzt.1 hzt.2).trans
      (mul_le_mul_of_nonneg_left
        (frequencyMajorant_le_annulusWedges hr0 hlambda hz) hC)
  have hregionFull : normalizedRegionIntegral f (squareAnnulus r0 lambda) ≤
      normalizedFrequencyIntegral W := by
    unfold normalizedRegionIntegral normalizedFrequencyIntegral
    apply mul_le_mul_of_nonneg_left _ normalizedFactorSq_nonneg
    calc
      (∫ z in squareAnnulus r0 lambda, f z ∂torusProductMeasure) ≤
          ∫ z in squareAnnulus r0 lambda, W z ∂torusProductMeasure := hregionMono
      _ ≤ ∫ z in Set.univ, W z ∂torusProductMeasure := by
        simpa only [setIntegral_univ] using setIntegral_le_integral
          (s := squareAnnulus r0 lambda) hWInt
          (Filter.Eventually.of_forall fun z => hWNonneg z)
  have hWIntegral : normalizedFrequencyIntegral W =
      C * (normalizedFrequencyIntegral (annulusWedgeX r0 lambda) +
        normalizedFrequencyIntegral (annulusWedgeY r0 lambda)) := by
    unfold normalizedFrequencyIntegral normalizedRegionIntegral
    simp only [setIntegral_univ, W, integral_const_mul,
      integral_add hXInt hYInt]
    ring
  calc
    normalizedRegionIntegral f (squareAnnulus r0 lambda) ≤
        normalizedFrequencyIntegral W := hregionFull
    _ = C * (normalizedFrequencyIntegral (annulusWedgeX r0 lambda) +
        normalizedFrequencyIntegral (annulusWedgeY r0 lambda)) := hWIntegral
    _ ≤ C * (8 + 8) := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact add_le_add
        (normalizedFrequencyIntegral_annulusWedgeX_le_eight hr0 hr0One hlambda)
        (normalizedFrequencyIntegral_annulusWedgeY_le_eight hr0 hr0One hlambda)
    _ = 16 * C := by ring

/-- The three regions cover frequency space. Overlap between the small and
outer regions is harmless and is handled by integral monotonicity. -/
theorem frequencyRegions_cover (r0 lambda : ℝ) :
    (smallSquare lambda ∪ squareAnnulus r0 lambda) ∪ outerRegion r0 = Set.univ := by
  ext z
  constructor
  · exact fun _ => Set.mem_univ z
  · intro _hz
    by_cases hs : squareRadius z ≤ Real.sqrt lambda
    · exact Or.inl (Or.inl hs)
    · have hs' : Real.sqrt lambda < squareRadius z := lt_of_not_ge hs
      by_cases ho : r0 / 2 ≤ squareRadius z
      · exact Or.inr ho
      · exact Or.inl (Or.inr ⟨hs', lt_of_not_ge ho⟩)

/-- A nonnegative integrable density is bounded by the sum of its three
regional integrals. -/
theorem normalizedFrequencyIntegral_le_region_sum {f : ℝ × ℝ → ℝ}
    (r0 lambda : ℝ) (hf : Integrable f torusProductMeasure)
    (hfNonneg : ∀ z, 0 ≤ f z) :
    normalizedFrequencyIntegral f ≤
      normalizedRegionIntegral f (smallSquare lambda) +
      normalizedRegionIntegral f (squareAnnulus r0 lambda) +
      normalizedRegionIntegral f (outerRegion r0) := by
  let s := smallSquare lambda
  let a := squareAnnulus r0 lambda
  let o := outerRegion r0
  have hsMeas : MeasurableSet s := measurableSet_smallSquare lambda
  have haMeas : MeasurableSet a := measurableSet_squareAnnulus r0 lambda
  have hoMeas : MeasurableSet o := measurableSet_outerRegion r0
  have hsInt : Integrable (s.indicator f) torusProductMeasure :=
    hf.indicator hsMeas
  have haInt : Integrable (a.indicator f) torusProductMeasure :=
    hf.indicator haMeas
  have hoInt : Integrable (o.indicator f) torusProductMeasure :=
    hf.indicator hoMeas
  have hindNonneg (t : Set (ℝ × ℝ)) (z : ℝ × ℝ) :
      0 ≤ t.indicator f z :=
    Set.indicator_nonneg (fun x _hx => hfNonneg x) z
  have hpoint : f ≤ s.indicator f + a.indicator f + o.indicator f := by
    intro z
    change f z ≤ s.indicator f z + a.indicator f z + o.indicator f z
    have hz : z ∈ (s ∪ a) ∪ o := by
      dsimp [s, a, o]
      rw [frequencyRegions_cover]
      exact Set.mem_univ z
    rcases hz with (hzs | hza) | hzo
    · rw [Set.indicator_of_mem hzs]
      nlinarith [hindNonneg a z, hindNonneg o z]
    · rw [Set.indicator_of_mem hza]
      nlinarith [hindNonneg s z, hindNonneg o z]
    · rw [Set.indicator_of_mem hzo]
      nlinarith [hindNonneg s z, hindNonneg a z]
  have hraw : (∫ z, f z ∂torusProductMeasure) ≤
      (∫ z in s, f z ∂torusProductMeasure) +
      (∫ z in a, f z ∂torusProductMeasure) +
      (∫ z in o, f z ∂torusProductMeasure) := by
    have hsumInt : Integrable (fun z =>
        (s.indicator f z + a.indicator f z) + o.indicator f z)
        torusProductMeasure := (hsInt.add haInt).add hoInt
    have hmono : (∫ z, f z ∂torusProductMeasure) ≤
        ∫ z, (s.indicator f z + a.indicator f z) + o.indicator f z
          ∂torusProductMeasure := by
      apply integral_mono hf hsumInt
      intro z
      exact hpoint z
    calc
      (∫ z, f z ∂torusProductMeasure) ≤
          ∫ z, (s.indicator f z + a.indicator f z) + o.indicator f z
            ∂torusProductMeasure := hmono
      _ = (∫ z, s.indicator f z ∂torusProductMeasure) +
          (∫ z, a.indicator f z ∂torusProductMeasure) +
          (∫ z, o.indicator f z ∂torusProductMeasure) := by
        calc
          (∫ z, (s.indicator f z + a.indicator f z) + o.indicator f z
              ∂torusProductMeasure) =
              (∫ z, s.indicator f z + a.indicator f z ∂torusProductMeasure) +
              ∫ z, o.indicator f z ∂torusProductMeasure := by
            simpa only [Pi.add_apply] using
              (integral_add (hsInt.add haInt) hoInt)
          _ = ((∫ z, s.indicator f z ∂torusProductMeasure) +
              ∫ z, a.indicator f z ∂torusProductMeasure) +
              ∫ z, o.indicator f z ∂torusProductMeasure := by
            rw [show (∫ z, s.indicator f z + a.indicator f z
                ∂torusProductMeasure) =
                (∫ z, s.indicator f z ∂torusProductMeasure) +
                ∫ z, a.indicator f z ∂torusProductMeasure by
              simpa only [Pi.add_apply] using (integral_add hsInt haInt)]
      _ = (∫ z in s, f z ∂torusProductMeasure) +
          (∫ z in a, f z ∂torusProductMeasure) +
          (∫ z in o, f z ∂torusProductMeasure) := by
        rw [integral_indicator hsMeas, integral_indicator haMeas,
          integral_indicator hoMeas]
  unfold normalizedFrequencyIntegral normalizedRegionIntegral
  rw [setIntegral_univ]
  calc
    (2 * Real.pi)⁻¹ ^ 2 * (∫ z, f z ∂torusProductMeasure) ≤
        (2 * Real.pi)⁻¹ ^ 2 *
          ((∫ z in s, f z ∂torusProductMeasure) +
          (∫ z in a, f z ∂torusProductMeasure) +
          (∫ z in o, f z ∂torusProductMeasure)) :=
      mul_le_mul_of_nonneg_left hraw normalizedFactorSq_nonneg
    _ = (2 * Real.pi)⁻¹ ^ 2 * (∫ z in smallSquare lambda, f z ∂torusProductMeasure) +
        (2 * Real.pi)⁻¹ ^ 2 * (∫ z in squareAnnulus r0 lambda, f z ∂torusProductMeasure) +
        (2 * Real.pi)⁻¹ ^ 2 * (∫ z in outerRegion r0, f z ∂torusProductMeasure) := by
      dsimp [s, a, o]
      ring

theorem frequencyMajorant_le_inv_lambda {r0 lambda : ℝ} (hlambda : 0 < lambda)
    (p : Fin 2 → ℝ) : Operator.frequencyMajorant r0 lambda p ≤ 1 / lambda := by
  have hthetaNonneg : 0 ≤ Operator.theta p := by
    rw [operator_theta_eq]
    exact theta_nonneg p
  have hdenPos : 0 < lambda + Operator.theta p :=
    add_pos_of_pos_of_nonneg hlambda hthetaNonneg
  calc
    Operator.frequencyMajorant r0 lambda p ≤
        Operator.driftlessMajorant lambda p := min_le_left _ _
    _ ≤ 1 / lambda := by
      unfold Operator.driftlessMajorant
      rw [one_div, one_div]
      exact (inv_le_inv₀ hdenPos hlambda).2 (le_add_of_nonneg_right hthetaNonneg)

private theorem frequencyDensity_integrable {f : ℝ × ℝ → ℝ}
    {C r0 lambda : ℝ} (hC : 0 ≤ C) (hlambda : 0 < lambda)
    (hf : Measurable f) (hfNonneg : ∀ z, 0 ≤ f z)
    (hpoint : ∀ z, z.1 ∈ torus → z.2 ∈ torus →
      f z ≤ C * Operator.frequencyMajorant r0 lambda ![z.1, z.2]) :
    Integrable f torusProductMeasure := by
  have hconst : Integrable (fun _ : ℝ × ℝ => C / lambda) torusProductMeasure :=
    integrable_const _
  apply Integrable.mono' hconst hf.aestronglyMeasurable
  filter_upwards [ae_mem_torusProduct] with z hzt
  have hle : f z ≤ C / lambda := calc
    f z ≤ C * Operator.frequencyMajorant r0 lambda ![z.1, z.2] :=
      hpoint z hzt.1 hzt.2
    _ ≤ C * (1 / lambda) := mul_le_mul_of_nonneg_left
      (frequencyMajorant_le_inv_lambda hlambda _) hC
    _ = C / lambda := by ring
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hfNonneg z),
    abs_of_nonneg (div_nonneg hC hlambda.le)] using hle

/-- Non-circular constructor for `RegionalIntegralBounds`. Its three fields
are consequences of the separately proved small-square, square-annulus, and
outer-region integral estimates. -/
def regionalIntegralBoundsOfFrequencyBound
    (green : ℝ → ℝ) (density : ℝ → ℝ × ℝ → ℝ) (r0 C : ℝ)
    (hr0 : 0 < r0) (hr0One : r0 < 1) (hC : 0 ≤ C)
    (hdensityMeas : ∀ lambda, Measurable (density lambda))
    (hdensityNonneg : ∀ lambda z, 0 ≤ density lambda z)
    (hgreen : ∀ lambda, 0 < lambda → lambda ≤ 1 →
      green lambda ≤ normalizedFrequencyIntegral (density lambda))
    (hpoint : ∀ lambda, 0 < lambda → lambda ≤ 1 → ∀ z,
      z.1 ∈ torus → z.2 ∈ torus →
      density lambda z ≤
        C * Operator.frequencyMajorant r0 lambda ![z.1, z.2]) :
    Operator.RegionalIntegralBounds green := by
  refine
    { smallBound := C
      middleCoefficient := 8 * C
      outerBound := C * (2 * Real.pi ^ 2 / r0 ^ 2)
      small_nonneg := hC
      middle_nonneg := mul_nonneg (by norm_num) hC
      outer_nonneg := mul_nonneg hC (by positivity)
      bound := ?_ }
  intro lambda hlambda hlambdaOne
  have hdInt : Integrable (density lambda) torusProductMeasure :=
    frequencyDensity_integrable hC hlambda (hdensityMeas lambda)
      (hdensityNonneg lambda) (hpoint lambda hlambda hlambdaOne)
  have hdecomp := normalizedFrequencyIntegral_le_region_sum r0 lambda hdInt
    (hdensityNonneg lambda)
  have hsmall := smallSquare_frequency_integral_le hC hlambda hlambdaOne
    (hdensityMeas lambda) (hdensityNonneg lambda)
    (hpoint lambda hlambda hlambdaOne)
  have hmiddle := squareAnnulus_integral_le hC hr0 hr0One hlambda
    (hdensityMeas lambda) (hdensityNonneg lambda)
    (hpoint lambda hlambda hlambdaOne)
  have houter := outerRegion_integral_le hC hr0 hlambda
    (hdensityMeas lambda) (hdensityNonneg lambda)
    (hpoint lambda hlambda hlambdaOne)
  calc
    green lambda ≤ normalizedFrequencyIntegral (density lambda) :=
      hgreen lambda hlambda hlambdaOne
    _ ≤ normalizedRegionIntegral (density lambda) (smallSquare lambda) +
        normalizedRegionIntegral (density lambda) (squareAnnulus r0 lambda) +
        normalizedRegionIntegral (density lambda) (outerRegion r0) := hdecomp
    _ ≤ C + 16 * C + C * (2 * Real.pi ^ 2 / r0 ^ 2) := by
      gcongr
    _ = C + (8 * C) * Operator.logarithmicTail +
        C * (2 * Real.pi ^ 2 / r0 ^ 2) := by
      rw [Operator.logarithmicTail_eq_two]
      ring

end Manhattan.Estimates
