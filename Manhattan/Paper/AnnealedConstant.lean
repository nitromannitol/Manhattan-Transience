import Manhattan.Paper.FrequencyBound

/-!
# `thm:annealed` with the constant `2048`

`thm:annealed` (`paper/arxiv/main.tex:180-188`, proof at `:1094-1121`): for every
`λ ∈ (0,1]`, `∫₀^∞ e^{-λt} p̄_t(0,0) dt ≤ 2048`, and `∫₀^∞ p̄_t(0,0) dt ≤ 2048`.

The proof integrates three bounds on `r_λ(p)`, each a function of `a(p)` alone
(`greenRadial`): `1/λ` on `a(p) ≤ √λ`; `prop:frequency` with
`[1 + log₊(1/(√λ + a))] ≥ [1 + log(1/a)]/2` on `√λ < a(p) < 1/4`; and
`π²/(2a(p)²)` on `a(p) ≥ 1/4` (`concreteGreenDensity_le_greenRadial`).  The
square `{a(p) ≤ b}` has normalized measure `b²/π²`, so a function of `a(p)`
integrates to `(2/π²) ∫₀^π b φ(b) db` (`normalizedFrequencyIntegral_le_radial`,
stated as an upper bound).  The three pieces give
`1/π² + 2^{7/2}·2048/(π²√(1 + log 4)) + log(4π) < 2048`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal
open Manhattan Manhattan.V4.Frequency Manhattan.Estimates

namespace Manhattan.Paper

noncomputable section

/-! ### The radial majorant -/

/-- `2048 · 2^{3/2}`. -/
def middleConstant : ℝ := 2048 * (2 * Real.sqrt 2)

theorem middleConstant_pos : 0 < middleConstant := by
  unfold middleConstant
  positivity

/-- The bound on `r_λ(p)` as a function of `b = a(p)`. -/
def greenRadial (lambda b : ℝ) : ℝ :=
  if b ≤ Real.sqrt lambda then lambda⁻¹
  else if b < 1 / 4 then middleConstant * annulusKernel b / b
  else Real.pi ^ 2 / (2 * b ^ 2)

theorem maxFrequency_concreteFrequency (z : ℝ × ℝ) :
    Operator.maxFrequency (Manhattan.Glue.concreteFrequency z) = squareRadius z := by
  simp [Operator.maxFrequency, Manhattan.Glue.concreteFrequency, squareRadius]

/-- On `√λ < a < 1/4`: `1 + log₊(1/(√λ + a)) ≥ (1 + log(1/a))/2`. -/
theorem half_le_v4LogScale {lambda : ℝ} (hlambda : 0 < lambda) {p : Fin 2 → ℝ}
    (hlow : Real.sqrt lambda < Operator.maxFrequency p)
    (hhigh : Operator.maxFrequency p < 1 / 4) :
    (1 - Real.log (Operator.maxFrequency p)) / 2 ≤ v4LogScale lambda p := by
  set a := Operator.maxFrequency p with ha
  have hs := Real.sqrt_pos.2 hlambda
  have hapos : 0 < a := hs.trans hlow
  have hsum : Real.sqrt lambda + a ≤ 2 * a := by linarith
  have hlog1 : Real.log (1 / (Real.sqrt lambda + a)) ≥ -Real.log (2 * a) := by
    rw [one_div, Real.log_inv]
    exact neg_le_neg (Real.log_le_log (by positivity) hsum)
  have hlog2 : Real.log (2 * a) = Real.log 2 + Real.log a :=
    Real.log_mul (by norm_num) hapos.ne'
  have hloga : Real.log a < Real.log (1 / 4) := Real.log_lt_log hapos hhigh
  have hlog4 : Real.log (1 / 4 : ℝ) = -(2 * Real.log 2) := by
    rw [one_div, Real.log_inv, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  have hpos : Operator.logPos (1 / (Real.sqrt lambda + a)) ≥
      Real.log (1 / (Real.sqrt lambda + a)) := le_max_left _ _
  unfold v4LogScale
  rw [← ha]
  linarith

/-- **The three bounds of the proof of `thm:annealed`.** -/
theorem concreteGreenDensity_le_greenRadial {lambda : ℝ} (hlambda : 0 < lambda)
    (hlambda1 : lambda ≤ 1) {z : ℝ × ℝ} (hz1 : z.1 ∈ torus) (hz2 : z.2 ∈ torus) :
    Manhattan.Glue.concreteGreenDensity lambda z ≤ greenRadial lambda (squareRadius z) := by
  set p := Manhattan.Glue.concreteFrequency z with hp
  have hmax : Operator.maxFrequency p = squareRadius z := maxFrequency_concreteFrequency z
  rw [Manhattan.Glue.concreteGreenDensity_eq_resolventQuadratic hlambda z]
  have hdrift := Manhattan.Glue.concrete_resolventQuadratic_le_driftless hlambda p
  have hth := Manhattan.operatorTheta_nonneg p
  have hden : 0 < lambda + Operator.theta p := by linarith
  set b := squareRadius z with hb
  have hp0 : |p 0| ≤ Real.pi := abs_le.2 ⟨hz1.1.le, hz1.2⟩
  have hp1 : |p 1| ≤ Real.pi := abs_le.2 ⟨hz2.1.le, hz2.2⟩
  unfold greenRadial
  split_ifs with h1 h2
  · refine hdrift.trans ?_
    rw [Operator.driftlessMajorant, one_div]
    exact inv_anti₀ hlambda (by linarith)
  · -- the middle region, from `prop:frequency`
    have hs := Real.sqrt_pos.2 hlambda
    have hlow : Real.sqrt lambda < Operator.maxFrequency p := by rw [hmax]; exact lt_of_not_ge h1
    have hhigh : Operator.maxFrequency p < 1 / 4 := by rw [hmax]; exact h2
    have hbpos : 0 < b := by rw [← hmax]; exact hs.trans hlow
    have hfreq := frequencyBound_2048 lambda hlambda hlambda1 p hz1 hz2
    have hL := half_le_v4LogScale hlambda hlow hhigh
    rw [hmax] at hL
    set L := v4LogScale lambda p with hLdef
    set m := (1 - Real.log b) / 2 with hm
    have hlogb : Real.log b < 0 := Real.log_neg hbpos (by linarith)
    have hm0 : 0 < m := by rw [hm]; linarith
    have hL0 : 0 ≤ L := hm0.le.trans hL
    have hpow : m * Real.sqrt m ≤ L ^ (3 / 2 : ℝ) := by
      rw [rpow_three_halves hL0]
      exact mul_le_mul hL (Real.sqrt_le_sqrt hL) (Real.sqrt_nonneg _) hL0
    set A := Real.sqrt (1 - Real.log b) with hA
    have hA0 : 0 < A := Real.sqrt_pos.2 (by linarith)
    have hAm : A ^ 3 = 2 * Real.sqrt 2 * (m * Real.sqrt m) := by
      have h2m : 1 - Real.log b = 2 * m := by rw [hm]; ring
      rw [hA, h2m, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2) m]
      have hs2 := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
      have hsm := Real.sq_sqrt hm0.le
      ring_nf
      rw [show Real.sqrt 2 ^ 3 = Real.sqrt 2 ^ 2 * Real.sqrt 2 by ring, hs2,
        show Real.sqrt m ^ 3 = Real.sqrt m ^ 2 * Real.sqrt m by ring, hsm]
      ring
    have hmaj : v4Majorant lambda p ≤ 1 / (b ^ 2 * (m * Real.sqrt m)) := by
      rw [v4Majorant, hmax]
      have hq : 0 < b ^ 2 * (m * Real.sqrt m) := by positivity
      refine one_div_le_one_div_of_le hq ?_
      have := mul_le_mul_of_nonneg_left hpow (sq_nonneg b)
      linarith
    refine hfreq.trans ?_
    have hq : 0 < b ^ 2 * (m * Real.sqrt m) := by positivity
    have hgoal : 2048 * (1 / (b ^ 2 * (m * Real.sqrt m))) =
        middleConstant * annulusKernel b / b := by
      rw [middleConstant, annulusKernel, ← hA]
      have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
      rw [hAm]
      field_simp
    rw [← hgoal]
    exact mul_le_mul_of_nonneg_left hmaj (by norm_num)
  · -- the outer region, from the zero function
    have hb4 : 1 / 4 ≤ b := le_of_not_gt h2
    have hbpos : 0 < b := by linarith
    have hthb : 2 * b ^ 2 / Real.pi ^ 2 ≤ Operator.theta p := by
      have hd0 := V4.Energy.two_sq_div_pi_sq_le_dispersion hp0
      have hd1 := V4.Energy.two_sq_div_pi_sq_le_dispersion hp1
      have hn0 : 0 ≤ Estimates.dispersion (p 0) := Estimates.dispersion_nonneg _
      have hn1 : 0 ≤ Estimates.dispersion (p 1) := Estimates.dispersion_nonneg _
      have htheta : Operator.theta p = Estimates.dispersion (p 0) + Estimates.dispersion (p 1) := by
        rw [Operator.theta, Fin.sum_univ_two]
        rfl
      rw [htheta]
      have hbmax : b = max |p 0| |p 1| := by rw [← hmax]; rfl
      rcases le_total |p 1| |p 0| with h | h
      · rw [max_eq_left h] at hbmax
        rw [hbmax, sq_abs]
        linarith
      · rw [max_eq_right h] at hbmax
        rw [hbmax, sq_abs]
        linarith
    refine hdrift.trans ?_
    rw [Operator.driftlessMajorant, one_div]
    have hq : 0 < 2 * b ^ 2 / Real.pi ^ 2 := by positivity
    calc (lambda + Operator.theta p)⁻¹ ≤ (2 * b ^ 2 / Real.pi ^ 2)⁻¹ :=
          inv_anti₀ hq (by linarith)
      _ = Real.pi ^ 2 / (2 * b ^ 2) := by rw [inv_div]

/-! ### Integrating a function of `a(p)` -/

theorem normalizedFrequencyIntegral_eq_iterated' {f : ℝ × ℝ → ℝ}
    (hf : Integrable f torusProductMeasure) :
    normalizedFrequencyIntegral f =
      torusIntegral (fun x => torusIntegral (fun y => f (x, y))) := by
  rw [normalizedFrequencyIntegral, normalizedRegionIntegral, setIntegral_univ,
    torusProductMeasure]
  change Integrable f ((volume.restrict torus).prod (volume.restrict torus)) at hf
  have hf' : Integrable (Function.uncurry fun x y => f (x, y))
      ((volume.restrict torus).prod (volume.restrict torus)) := hf
  rw [← MeasureTheory.integral_integral hf']
  simp only [torusIntegral, integral_const_mul, smul_eq_mul]
  ring

theorem torusProductMeasure_eq_restrict :
    torusProductMeasure = (volume : Measure (ℝ × ℝ)).restrict (torus ×ˢ torus) := by
  rw [torusProductMeasure, Measure.prod_restrict]
  rfl

theorem integrable_torusProduct_of_bound {f : ℝ × ℝ → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ z, |f z| ≤ C) : Integrable f torusProductMeasure := by
  rw [torusProductMeasure_eq_restrict]
  have hfin : (volume : Measure (ℝ × ℝ)) (torus ×ˢ torus) ≠ ⊤ := by
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    exact ENNReal.mul_ne_top (by rw [torus]; exact measure_Ioc_lt_top.ne)
      (by rw [torus]; exact measure_Ioc_lt_top.ne)
  exact Integrable.mono' (integrableOn_const hfin (C := C)) hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hC z)

/-- The normalized integral of an even function over the circle. -/
theorem torusIntegral_comp_abs {h : ℝ → ℝ} (hm : Measurable h) {C : ℝ}
    (hC : ∀ x : ℝ, |x| ≤ Real.pi → |h (|x|)| ≤ C) :
    torusIntegral (fun x => h |x|) = Real.pi⁻¹ * ∫ u in (0:ℝ)..Real.pi, h u := by
  have hpi := Real.pi_pos
  have hint : ∀ a b : ℝ, -Real.pi ≤ a → a ≤ b → b ≤ Real.pi →
      IntervalIntegrable (fun x => h |x|) volume a b := by
    intro a b ha hab hb
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    refine Measure.integrableOn_of_bounded (M := C) measure_Ioc_lt_top.ne
      (hm.comp continuous_abs.measurable).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [Real.norm_eq_abs]
    exact hC x (abs_le.2 ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  have hsplit : (∫ x in (-Real.pi)..Real.pi, h |x|) =
      (∫ x in (-Real.pi)..0, h |x|) + ∫ x in (0:ℝ)..Real.pi, h |x| :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hint _ _ le_rfl (by linarith) (by linarith))
      (hint _ _ (by linarith) hpi.le le_rfl)).symm
  have hneg : (∫ x in (-Real.pi)..0, h |x|) = ∫ x in (0:ℝ)..Real.pi, h |x| := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := Real.pi) (fun x => h |x|)
    simp only [abs_neg, neg_zero] at this
    exact this.symm
  have hpos : (∫ x in (0:ℝ)..Real.pi, h |x|) = ∫ u in (0:ℝ)..Real.pi, h u := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le Real.pi_pos.le] at hx
    simp only [abs_of_nonneg hx.1]
  rw [torusIntegral, torus, ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
    hsplit, hneg, hpos, smul_eq_mul]
  field_simp
  ring

/-- The normalized measure of the strip `|y| ≤ u` is at most `u/π`. -/
theorem torusIntegral_indicator_abs_le {u : ℝ} (hu : 0 ≤ u) :
    torusIntegral (fun y : ℝ => if |y| ≤ u then (1 : ℝ) else 0) ≤ u / Real.pi := by
  have hset : (fun y : ℝ => if |y| ≤ u then (1 : ℝ) else 0) = (Icc (-u) u).indicator 1 := by
    funext y
    simp only [Set.indicator, Set.mem_Icc, abs_le, Pi.one_apply]
  rw [hset, torusIntegral, integral_indicator measurableSet_Icc, smul_eq_mul]
  have hle : (∫ y in Icc (-u) u, (1 : ℝ) ∂(volume.restrict torus)) ≤ 2 * u := by
    rw [Measure.restrict_restrict measurableSet_Icc, setIntegral_const, smul_eq_mul, mul_one]
    have hm : volume (Icc (-u) u ∩ torus) ≤ volume (Icc (-u) u) :=
      measure_mono Set.inter_subset_left
    rw [Measure.real]
    have hfin : volume (Icc (-u) u) ≠ ⊤ := measure_Icc_lt_top.ne
    have := ENNReal.toReal_mono hfin hm
    rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)] at this
    linarith
  have hpi := Real.pi_pos
  calc (2 * Real.pi)⁻¹ * ∫ y in Icc (-u) u, (1 : ℝ) ∂(volume.restrict torus)
      ≤ (2 * Real.pi)⁻¹ * (2 * u) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = u / Real.pi := by field_simp

/-- **A function of `a(p)` integrates against the density `2b/π²`.**  Upper
bound: a nonnegative density bounded by `φ(a(p))` on the torus has normalized
integral at most `(2/π²) ∫₀^π b φ(b) db`. -/
theorem normalizedFrequencyIntegral_le_radial {f : ℝ × ℝ → ℝ} {φ : ℝ → ℝ} {C : ℝ}
    (hf0 : ∀ z, 0 ≤ f z) (hφm : Measurable φ) (hφ0 : ∀ b, 0 ≤ φ b)
    (hφC : ∀ b, φ b ≤ C)
    (hf : ∀ z, z.1 ∈ torus → z.2 ∈ torus → f z ≤ φ (squareRadius z)) :
    normalizedFrequencyIntegral f ≤
      2 / Real.pi ^ 2 * ∫ b in (0:ℝ)..Real.pi, b * φ b := by
  classical
  have hpi := Real.pi_pos
  have hC0 : 0 ≤ C := (hφ0 0).trans (hφC 0)
  set g1 : ℝ × ℝ → ℝ := fun z => φ |z.1| * (if |z.2| ≤ |z.1| then 1 else 0) with hg1
  set g2 : ℝ × ℝ → ℝ := fun z => g1 (z.2, z.1) with hg2
  have hind : Measurable fun z : ℝ × ℝ => (if |z.2| ≤ |z.1| then (1 : ℝ) else 0) :=
    Measurable.ite (measurableSet_le (continuous_abs.measurable.comp measurable_snd)
      (continuous_abs.measurable.comp measurable_fst)) measurable_const measurable_const
  have hg1m : Measurable g1 := (hφm.comp (continuous_abs.measurable.comp measurable_fst)).mul hind
  have hg2m : Measurable g2 := hg1m.comp (measurable_snd.prodMk measurable_fst)
  have hg1b : ∀ z, |g1 z| ≤ C := by
    intro z
    simp only [hg1]
    split_ifs
    · rw [mul_one, abs_of_nonneg (hφ0 _)]
      exact hφC _
    · rw [mul_zero, abs_zero]
      exact hC0
  have hg2b : ∀ z, |g2 z| ≤ C := fun z => hg1b _
  have hg1i := integrable_torusProduct_of_bound hg1m hg1b
  have hg2i := integrable_torusProduct_of_bound hg2m hg2b
  -- (1) the pointwise comparison
  have hpt : ∀ z, z.1 ∈ torus → z.2 ∈ torus → f z ≤ g1 z + g2 z := by
    intro z h1 h2
    refine (hf z h1 h2).trans ?_
    simp only [hg2, hg1, squareRadius]
    rcases le_total |z.2| |z.1| with h | h
    · rw [max_eq_left h, if_pos h]
      have : 0 ≤ φ |z.2| * (if |z.1| ≤ |z.2| then 1 else 0) := by
        split_ifs <;> simp [hφ0]
      linarith
    · rw [max_eq_right h, if_pos h]
      have : 0 ≤ φ |z.1| * (if |z.2| ≤ |z.1| then 1 else 0) := by
        split_ifs <;> simp [hφ0]
      linarith
  have hmono : normalizedFrequencyIntegral f ≤ normalizedFrequencyIntegral (fun z => g1 z + g2 z) := by
    unfold normalizedFrequencyIntegral normalizedRegionIntegral
    rw [setIntegral_univ, setIntegral_univ]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall hf0) (hg1i.add hg2i) ?_
    rw [torusProductMeasure_eq_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_torus.prod measurableSet_torus)] with z hz
    exact hpt z hz.1 hz.2
  -- (2) the two halves are equal
  have hswap : normalizedFrequencyIntegral g2 = normalizedFrequencyIntegral g1 := by
    unfold normalizedFrequencyIntegral normalizedRegionIntegral
    rw [setIntegral_univ, setIntegral_univ, torusProductMeasure]
    congr 1
    simpa [hg2, Prod.swap] using
      (MeasureTheory.integral_prod_swap
        (μ := volume.restrict torus) (ν := volume.restrict torus) g1)
  have hadd : normalizedFrequencyIntegral (fun z => g1 z + g2 z) =
      normalizedFrequencyIntegral g1 + normalizedFrequencyIntegral g2 := by
    unfold normalizedFrequencyIntegral normalizedRegionIntegral
    rw [setIntegral_univ, setIntegral_univ, setIntegral_univ, integral_add hg1i hg2i]
    ring
  -- (3) one half
  have hhalf : normalizedFrequencyIntegral g1 ≤
      Real.pi⁻¹ * (Real.pi⁻¹ * ∫ b in (0:ℝ)..Real.pi, b * φ b) := by
    rw [normalizedFrequencyIntegral_eq_iterated' hg1i]
    have hinner : ∀ x : ℝ, torusIntegral (fun y => g1 (x, y)) =
        φ |x| * torusIntegral (fun y : ℝ => if |y| ≤ |x| then (1 : ℝ) else 0) := by
      intro x
      simp only [hg1, torusIntegral, ← integral_const_mul, smul_eq_mul]
      ring_nf
    have hh : ∀ x : ℝ, torusIntegral (fun y => g1 (x, y)) ≤ Real.pi⁻¹ * (|x| * φ |x|) := by
      intro x
      rw [hinner]
      have := torusIntegral_indicator_abs_le (abs_nonneg x)
      calc φ |x| * torusIntegral (fun y : ℝ => if |y| ≤ |x| then (1 : ℝ) else 0)
          ≤ φ |x| * (|x| / Real.pi) := mul_le_mul_of_nonneg_left this (hφ0 _)
        _ = Real.pi⁻¹ * (|x| * φ |x|) := by ring
    have hmeasIn : Measurable fun x : ℝ => torusIntegral (fun y => g1 (x, y)) := by
      have : (fun x : ℝ => torusIntegral (fun y => g1 (x, y))) = fun x =>
          (2 * Real.pi)⁻¹ * ∫ y, g1 (x, y) ∂(volume.restrict torus) := by
        funext x
        rw [torusIntegral, smul_eq_mul]
      rw [this]
      exact measurable_const.mul (hg1m.stronglyMeasurable.integral_prod_right'
        (ν := volume.restrict torus)).measurable
    have hb1 : ∀ x : ℝ, |torusIntegral (fun y => g1 (x, y))| ≤ C := by
      intro x
      simp only [torusIntegral, smul_eq_mul]
      rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < (2 * Real.pi)⁻¹)]
      have h := norm_integral_le_of_norm_le_const (μ := volume.restrict torus)
        (f := fun y => g1 (x, y)) (C := C) (Filter.Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs]; exact hg1b _)
      rw [Real.norm_eq_abs, measureReal_def, Measure.restrict_apply_univ, torus,
        Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)] at h
      calc (2 * Real.pi)⁻¹ * |∫ y, g1 (x, y) ∂(volume.restrict torus)|
          ≤ (2 * Real.pi)⁻¹ * (C * (Real.pi - -Real.pi)) :=
            mul_le_mul_of_nonneg_left h (by positivity)
        _ = C := by field_simp; ring
    have hmono2 : torusIntegral (fun x => torusIntegral (fun y => g1 (x, y))) ≤
        torusIntegral (fun x => Real.pi⁻¹ * (|x| * φ |x|)) := by
      unfold torusIntegral
      rw [smul_eq_mul, smul_eq_mul]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine integral_mono (Integrable.mono' (integrableOn_const (C := C)
        (by rw [torus]; exact measure_Ioc_lt_top.ne)) hmeasIn.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hb1 x)) ?_
        (fun x => by
          have := hh x
          simp only [torusIntegral, smul_eq_mul] at this ⊢
          exact this)
      refine Integrable.mono' (integrableOn_const (C := Real.pi⁻¹ * (4 * C))
        (by rw [torus]; exact measure_Ioc_lt_top.ne)) ?_ ?_
      · exact (measurable_const.mul (continuous_abs.measurable.mul (hφm.comp continuous_abs.measurable))).aestronglyMeasurable
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
        rw [Real.norm_eq_abs, abs_of_nonneg (by have := hφ0 |x|; positivity)]
        have hxa : |x| ≤ Real.pi := abs_le.2 ⟨hx.1.le, hx.2⟩
        have hpi4 : Real.pi ≤ 4 := Real.pi_le_four
        have := hφC |x|
        have h0 := hφ0 |x|
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        nlinarith [abs_nonneg x]
    refine hmono2.trans (le_of_eq ?_)
    have hφx : ∀ u, |u * φ u| ≤ C * (|u|) := by
      intro u
      rw [abs_mul, abs_of_nonneg (hφ0 u)]
      nlinarith [abs_nonneg u, hφC u, hφ0 u]
    rw [show (fun x : ℝ => Real.pi⁻¹ * (|x| * φ |x|)) =
        fun x => (fun u => Real.pi⁻¹ * (u * φ u)) |x| by rfl]
    rw [torusIntegral_comp_abs (h := fun u => Real.pi⁻¹ * (u * φ u))
      (measurable_const.mul (measurable_id.mul hφm)) (C := C)]
    · rw [intervalIntegral.integral_const_mul]
    · intro x hx
      rw [abs_mul, abs_of_pos (inv_pos.2 hpi), abs_mul, abs_abs,
        abs_of_nonneg (hφ0 _)]
      have h1 := hφC |x|
      have h0 := hφ0 |x|
      have h2 : |x| * φ |x| ≤ Real.pi * C := by nlinarith [abs_nonneg x]
      calc Real.pi⁻¹ * (|x| * φ |x|) ≤ Real.pi⁻¹ * (Real.pi * C) :=
            mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 hpi.le)
        _ = C := by field_simp
  rw [hadd, hswap] at hmono
  have h2 : 2 / Real.pi ^ 2 * ∫ b in (0:ℝ)..Real.pi, b * φ b =
      2 * (Real.pi⁻¹ * (Real.pi⁻¹ * ∫ b in (0:ℝ)..Real.pi, b * φ b)) := by
    field_simp
  rw [h2]
  linarith

/-! ### The one-dimensional integral -/

theorem measurable_annulusKernel : Measurable annulusKernel := by
  unfold annulusKernel
  fun_prop

theorem measurable_greenRadial (lambda : ℝ) : Measurable (greenRadial lambda) := by
  unfold greenRadial
  refine Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_const ?_
  refine Measurable.ite (measurableSet_lt measurable_id measurable_const) ?_ ?_
  · exact (measurable_const.mul measurable_annulusKernel).div measurable_id
  · exact measurable_const.div (measurable_const.mul (measurable_id.pow_const 2))

theorem annulusKernel_nonneg {b : ℝ} (hb : 0 < b) : 0 ≤ annulusKernel b := by
  unfold annulusKernel
  positivity

/-- `annulusKernel b ≤ 1/b` for `0 < b ≤ 1`. -/
theorem annulusKernel_le_inv {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) : annulusKernel b ≤ b⁻¹ := by
  unfold annulusKernel
  have hlog := Real.log_nonpos hb.le hb1
  have h1 : 1 ≤ Real.sqrt (1 - Real.log b) := Real.one_le_sqrt.mpr (by linarith)
  have h3 : 1 ≤ Real.sqrt (1 - Real.log b) ^ 3 := one_le_pow₀ h1
  rw [mul_inv]
  have : (Real.sqrt (1 - Real.log b) ^ 3)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h3
  have hbinv : 0 < b⁻¹ := inv_pos.2 hb
  nlinarith

theorem greenRadial_nonneg {lambda : ℝ} (hlambda : 0 < lambda) (b : ℝ) :
    0 ≤ greenRadial lambda b := by
  unfold greenRadial
  split_ifs with h1 h2
  · positivity
  · have hb : 0 < b := (Real.sqrt_pos.2 hlambda).trans (lt_of_not_ge h1)
    have := annulusKernel_nonneg hb
    have := middleConstant_pos
    positivity
  · positivity

theorem greenRadial_le {lambda : ℝ} (hlambda : 0 < lambda) (b : ℝ) :
    greenRadial lambda b ≤ lambda⁻¹ + middleConstant * lambda⁻¹ + 16 * Real.pi ^ 2 := by
  have hK := middleConstant_pos
  have hl : 0 < lambda⁻¹ := inv_pos.2 hlambda
  have hpi := Real.pi_pos
  unfold greenRadial
  split_ifs with h1 h2
  · have : 0 ≤ middleConstant * lambda⁻¹ := by positivity
    have : 0 ≤ 16 * Real.pi ^ 2 := by positivity
    linarith
  · have hs := Real.sqrt_pos.2 hlambda
    have hb : Real.sqrt lambda < b := lt_of_not_ge h1
    have hbpos : 0 < b := hs.trans hb
    have hak := annulusKernel_le_inv hbpos (by linarith)
    have hb2 : lambda ≤ b ^ 2 := by
      have := Real.sq_sqrt hlambda.le
      nlinarith
    have hinv : (b ^ 2)⁻¹ ≤ lambda⁻¹ := inv_anti₀ hlambda hb2
    have hstep : middleConstant * annulusKernel b / b ≤ middleConstant * (b ^ 2)⁻¹ := by
      rw [mul_div_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hK.le
      calc annulusKernel b / b ≤ b⁻¹ / b := div_le_div_of_nonneg_right hak hbpos.le
        _ = (b ^ 2)⁻¹ := by field_simp
    have := mul_le_mul_of_nonneg_left hinv hK.le
    nlinarith
  · have hb4 : 1 / 4 ≤ b := le_of_not_gt h2
    have hbpos : 0 < b := by linarith
    have : Real.pi ^ 2 / (2 * b ^ 2) ≤ 8 * Real.pi ^ 2 := by
      rw [div_le_iff₀ (by positivity)]
      have hb2 : 1 / 16 ≤ b ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hb2 (sq_nonneg Real.pi)]
    nlinarith

theorem intervalIntegrable_of_bound {f : ℝ → ℝ} (hf : Measurable f) {a b C : ℝ} (hab : a ≤ b)
    (hC : ∀ x ∈ Ioc a b, |f x| ≤ C) : IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  refine Measure.integrableOn_of_bounded (M := C) measure_Ioc_lt_top.ne hf.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  rw [Real.norm_eq_abs]
  exact hC x hx

/-- `∫_s^{1/4} db/(b (1 + log(1/b))^{3/2}) ≤ 2/√(1 + log 4)`. -/
theorem integral_annulusKernel_le {s : ℝ} (hs : 0 < s) (hs4 : s ≤ 1 / 4) :
    (∫ x in s..(1 / 4 : ℝ), annulusKernel x) ≤ 2 / Real.sqrt (1 + Real.log 4) := by
  have hderiv : ∀ x ∈ Set.uIcc s (1 / 4 : ℝ),
      HasDerivAt (fun y : ℝ => 2 * (Real.sqrt (1 - Real.log y))⁻¹) (annulusKernel x) x := by
    intro x hx
    rw [Set.uIcc_of_le hs4] at hx
    exact annulusKernel_hasDerivAt (hs.trans_le hx.1) (hx.2.trans (by norm_num))
  have hint : IntervalIntegrable annulusKernel volume s (1 / 4) := by
    refine intervalIntegrable_of_bound measurable_annulusKernel hs4 (C := s⁻¹) ?_
    intro x hx
    have hxpos : 0 < x := hs.trans hx.1
    rw [abs_of_nonneg (annulusKernel_nonneg hxpos)]
    exact (annulusKernel_le_inv hxpos (by linarith [hx.2])).trans
      (inv_anti₀ hs hx.1.le)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have hleft : 0 ≤ 2 * (Real.sqrt (1 - Real.log s))⁻¹ := by positivity
  have hlog4 : Real.log (1 / 4 : ℝ) = -Real.log 4 := by
    rw [one_div, Real.log_inv]
  rw [hlog4, sub_neg_eq_add, div_eq_mul_inv]
  linarith

/-- **The one-dimensional integral of the three bounds.** -/
theorem integral_mul_greenRadial_le {lambda : ℝ} (hlambda : 0 < lambda) (hlambda1 : lambda ≤ 1) :
    (∫ b in (0:ℝ)..Real.pi, b * greenRadial lambda b) ≤
      1 / 2 + middleConstant * (2 / Real.sqrt (1 + Real.log 4)) +
        Real.pi ^ 2 / 2 * Real.log (4 * Real.pi) := by
  have hpi := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  set s := Real.sqrt lambda with hsdef
  have hs : 0 < s := Real.sqrt_pos.2 hlambda
  have hs1 : s ≤ 1 := Real.sqrt_le_one.mpr hlambda1
  have hsq : s ^ 2 = lambda := Real.sq_sqrt hlambda.le
  have hK := middleConstant_pos
  set Cb := lambda⁻¹ + middleConstant * lambda⁻¹ + 16 * Real.pi ^ 2 with hCb
  have hGm := measurable_greenRadial lambda
  have hFm : Measurable fun b => b * greenRadial lambda b := measurable_id.mul hGm
  have hFint : ∀ a c : ℝ, 0 ≤ a → a ≤ c → c ≤ Real.pi →
      IntervalIntegrable (fun b => b * greenRadial lambda b) volume a c := by
    intro a c ha hac hc
    refine intervalIntegrable_of_bound hFm hac (C := Real.pi * Cb) ?_
    intro x hx
    have hx0 : 0 ≤ x := ha.trans hx.1.le
    rw [abs_mul, abs_of_nonneg hx0, abs_of_nonneg (greenRadial_nonneg hlambda x)]
    exact mul_le_mul (hx.2.trans hc) (greenRadial_le hlambda x)
      (greenRadial_nonneg hlambda x) hpi.le
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := s)
    (hFint 0 s le_rfl hs.le (by linarith)) (hFint s Real.pi hs.le (by linarith) le_rfl)]
  -- the small square
  have h1 : (∫ b in (0:ℝ)..s, b * greenRadial lambda b) = 1 / 2 := by
    have hcongr : (∫ b in (0:ℝ)..s, b * greenRadial lambda b) =
        ∫ b in (0:ℝ)..s, b * lambda⁻¹ := by
      refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun x hx => ?_)
      rw [Set.uIoc_of_le hs.le] at hx
      rw [greenRadial, if_pos (show x ≤ Real.sqrt lambda from hx.2)]
    rw [hcongr, intervalIntegral.integral_mul_const, integral_id, hsq]
    field_simp
    ring
  -- the rest of the circle
  set G2 : ℝ → ℝ := fun x => if x < 1 / 4 then middleConstant * annulusKernel x
    else Real.pi ^ 2 / 2 * x⁻¹ with hG2
  have h2 : (∫ b in s..Real.pi, b * greenRadial lambda b) = ∫ b in s..Real.pi, G2 b := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun x hx => ?_)
    rw [Set.uIoc_of_le (by linarith)] at hx
    have hxs : ¬ x ≤ s := not_le.mpr hx.1
    have hxpos : 0 < x := hs.trans hx.1
    rw [greenRadial, if_neg (show ¬ x ≤ Real.sqrt lambda from hxs)]
    simp only [hG2]
    split_ifs
    · rw [← mul_div_assoc, mul_div_cancel_left₀ _ hxpos.ne']
    · field_simp
  have hG2m : Measurable G2 := by
    refine Measurable.ite (measurableSet_lt measurable_id measurable_const)
      (measurable_const.mul measurable_annulusKernel) (measurable_const.mul measurable_inv)
  have hG2int : ∀ a c : ℝ, s ≤ a → a ≤ c → IntervalIntegrable G2 volume a c := by
    intro a c ha hac
    refine intervalIntegrable_of_bound hG2m hac (C := middleConstant * s⁻¹ +
      Real.pi ^ 2 / 2 * s⁻¹) ?_
    intro x hx
    have hxpos : 0 < x := hs.trans_le (ha.trans hx.1.le)
    have hxs : s ≤ x := ha.trans hx.1.le
    have hxinv : x⁻¹ ≤ s⁻¹ := inv_anti₀ hs hxs
    simp only [hG2]
    split_ifs with hx4
    · rw [abs_of_nonneg (mul_nonneg hK.le (annulusKernel_nonneg hxpos))]
      have := annulusKernel_le_inv hxpos (by linarith)
      have := mul_le_mul_of_nonneg_left (this.trans hxinv) hK.le
      have : 0 ≤ Real.pi ^ 2 / 2 * s⁻¹ := by positivity
      linarith
    · rw [abs_of_nonneg (by positivity)]
      have := mul_le_mul_of_nonneg_left hxinv (by positivity : (0:ℝ) ≤ Real.pi ^ 2 / 2)
      have : 0 ≤ middleConstant * s⁻¹ := by positivity
      linarith
  have hlogint : ∀ a : ℝ, 0 < a → a ≤ Real.pi →
      (∫ x in a..Real.pi, Real.pi ^ 2 / 2 * x⁻¹) = Real.pi ^ 2 / 2 * Real.log (Real.pi / a) := by
    intro a ha _
    rw [intervalIntegral.integral_const_mul, integral_inv_of_pos ha hpi]
  have hlogle : ∀ a : ℝ, 1 / 4 ≤ a → a ≤ Real.pi →
      Real.pi ^ 2 / 2 * Real.log (Real.pi / a) ≤ Real.pi ^ 2 / 2 * Real.log (4 * Real.pi) := by
    intro a ha _
    refine mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) ?_) (by positivity)
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hKterm : 0 ≤ middleConstant * (2 / Real.sqrt (1 + Real.log 4)) := by positivity
  rw [h1, h2]
  rcases lt_or_ge s (1 / 4) with hs4 | hs4
  · rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1 / 4)
      (hG2int s (1 / 4) le_rfl hs4.le) (hG2int (1 / 4) Real.pi hs4.le (by linarith))]
    have hmid : (∫ x in s..(1 / 4 : ℝ), G2 x) ≤
        ∫ x in s..(1 / 4 : ℝ), middleConstant * annulusKernel x := by
      refine intervalIntegral.integral_mono_on hs4.le (hG2int s (1 / 4) le_rfl hs4.le) ?_ ?_
      · refine (intervalIntegrable_of_bound measurable_annulusKernel hs4.le (C := s⁻¹) ?_).const_mul
          middleConstant
        intro x hx
        have hxpos : 0 < x := hs.trans hx.1
        rw [abs_of_nonneg (annulusKernel_nonneg hxpos)]
        exact (annulusKernel_le_inv hxpos (by linarith [hx.2])).trans (inv_anti₀ hs hx.1.le)
      · intro x hx
        simp only [hG2]
        split_ifs with hx4
        · exact le_rfl
        · have hx14 : x = 1 / 4 := le_antisymm hx.2 (le_of_not_gt hx4)
          subst hx14
          -- at the endpoint: `2π² ≤ K · annulusKernel (1/4)`
          have hak : 1 ≤ annulusKernel (1 / 4) := by
            unfold annulusKernel
            have hlog4 : Real.log (1 / 4 : ℝ) = -Real.log 4 := by rw [one_div, Real.log_inv]
            rw [hlog4, sub_neg_eq_add]
            have hl4 : Real.log 4 < 1.4964 := by
              have h2 := Real.log_two_lt_d9
              rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
              push_cast
              linarith
            have hl4' : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
            have hsq : Real.sqrt (1 + Real.log 4) ≤ 1.58 := by
              rw [show (1.58 : ℝ) = Real.sqrt (1.58 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
              exact Real.sqrt_le_sqrt (by nlinarith)
            have hsq0 : 0 ≤ Real.sqrt (1 + Real.log 4) := Real.sqrt_nonneg _
            have hcube : Real.sqrt (1 + Real.log 4) ^ 3 ≤ 4 := by
              have : Real.sqrt (1 + Real.log 4) ^ 3 ≤ 1.58 ^ 3 :=
                pow_le_pow_left₀ hsq0 hsq 3
              nlinarith
            have hpos : 0 < 1 / 4 * Real.sqrt (1 + Real.log 4) ^ 3 := by
              have : 0 < Real.sqrt (1 + Real.log 4) := Real.sqrt_pos.2 (by linarith)
              positivity
            rw [one_le_inv₀ hpos]
            linarith
          have hKbig : 20 ≤ middleConstant := by
            unfold middleConstant
            have : 1 ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
            nlinarith
          have hpisq : Real.pi ^ 2 ≤ 10 := by nlinarith [Real.pi_lt_d2]
          have : Real.pi ^ 2 / 2 * (1 / 4 : ℝ)⁻¹ ≤ 20 := by nlinarith
          nlinarith
    have hmid2 : (∫ x in s..(1 / 4 : ℝ), middleConstant * annulusKernel x) ≤
        middleConstant * (2 / Real.sqrt (1 + Real.log 4)) := by
      rw [intervalIntegral.integral_const_mul]
      exact mul_le_mul_of_nonneg_left (integral_annulusKernel_le hs hs4.le) hK.le
    have hout : (∫ x in (1 / 4 : ℝ)..Real.pi, G2 x) =
        Real.pi ^ 2 / 2 * Real.log (4 * Real.pi) := by
      rw [← show Real.pi / (1 / 4) = 4 * Real.pi by field_simp,
        ← hlogint (1 / 4) (by norm_num) (by linarith)]
      refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun x hx => ?_)
      rw [Set.uIoc_of_le (by linarith)] at hx
      simp only [hG2, if_neg (not_lt.mpr hx.1.le)]
    linarith
  · have hout : (∫ x in s..Real.pi, G2 x) = Real.pi ^ 2 / 2 * Real.log (Real.pi / s) := by
      rw [← hlogint s hs (by linarith)]
      refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun x hx => ?_)
      rw [Set.uIoc_of_le (by linarith)] at hx
      simp only [hG2, if_neg (not_lt.mpr (hs4.trans hx.1.le))]
    rw [hout]
    have := hlogle s hs4 (by linarith)
    linarith

/-- The numerical value: `1/π² + 2^{7/2}·2048/(π²√(1 + log 4)) + log(4π) < 2048`. -/
theorem greenConstant_le_2048 :
    2 / Real.pi ^ 2 * (1 / 2 + middleConstant * (2 / Real.sqrt (1 + Real.log 4)) +
      Real.pi ^ 2 / 2 * Real.log (4 * Real.pi)) ≤ 2048 := by
  have hpi := Real.pi_pos
  have hpisq : (9.8696 : ℝ) ≤ Real.pi ^ 2 := Constant.pi_sq_ge
  have hl2 := Real.log_two_gt_d9
  have hlog4 : (1.25 : ℝ) ≤ Real.log 4 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    linarith
  have hX : (1.5 : ℝ) ≤ Real.sqrt (1 + Real.log 4) := by
    rw [show (1.5 : ℝ) = Real.sqrt (1.5 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hX0 : 0 < Real.sqrt (1 + Real.log 4) := by linarith
  have hs2 : Real.sqrt 2 ≤ 1.4143 := by
    rw [show (1.4143 : ℝ) = Real.sqrt (1.4143 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hK : middleConstant ≤ 5793 := by
    unfold middleConstant
    nlinarith
  have hK0 := middleConstant_pos
  have hfrac : 2 / Real.sqrt (1 + Real.log 4) ≤ 4 / 3 := by
    rw [div_le_iff₀ hX0]
    nlinarith
  have hKX : middleConstant * (2 / Real.sqrt (1 + Real.log 4)) ≤ 7724 := by
    have h0 : 0 ≤ 2 / Real.sqrt (1 + Real.log 4) := by positivity
    nlinarith
  have hlog : Real.log (4 * Real.pi) ≤ 4 * Real.pi - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hpi4 : Real.pi ≤ 3.1416 := by linarith [Real.pi_lt_d4]
  have hsplit : 2 / Real.pi ^ 2 * (1 / 2 + middleConstant * (2 / Real.sqrt (1 + Real.log 4)) +
      Real.pi ^ 2 / 2 * Real.log (4 * Real.pi)) =
      2 / Real.pi ^ 2 * (1 / 2 + middleConstant * (2 / Real.sqrt (1 + Real.log 4))) +
        Real.log (4 * Real.pi) := by
    field_simp
  rw [hsplit]
  have hc : 2 / Real.pi ^ 2 ≤ 2 / 9.8696 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpisq
  have hpos : 0 ≤ 1 / 2 + middleConstant * (2 / Real.sqrt (1 + Real.log 4)) := by positivity
  have := mul_le_mul hc (show 1 / 2 + middleConstant * (2 / Real.sqrt (1 + Real.log 4)) ≤ 7724.5
    by linarith) hpos (by norm_num)
  nlinarith

/-! ### `thm:annealed` -/

/-- The frequency integral of `r_λ` is at most `2048`, uniformly in `λ ∈ (0,1]`. -/
theorem normalizedGreenIntegral_le_2048 {lambda : ℝ} (hlambda : 0 < lambda)
    (hlambda1 : lambda ≤ 1) :
    normalizedFrequencyIntegral (Manhattan.Glue.concreteGreenDensity lambda) ≤ 2048 := by
  have hrad := normalizedFrequencyIntegral_le_radial (φ := greenRadial lambda)
    (Manhattan.Glue.concreteGreenDensity_nonneg lambda) (measurable_greenRadial lambda)
    (greenRadial_nonneg hlambda) (greenRadial_le hlambda)
    (fun z h1 h2 => concreteGreenDensity_le_greenRadial hlambda hlambda1 h1 h2)
  have hint := integral_mul_greenRadial_le hlambda hlambda1
  have hpi := Real.pi_pos
  have hmul := mul_le_mul_of_nonneg_left hint (by positivity : (0:ℝ) ≤ 2 / Real.pi ^ 2)
  exact hrad.trans (hmul.trans greenConstant_le_2048)

/-- **`thm:annealed`** (`paper/arxiv/main.tex:180-188`), with the constant `2048`
of the paper: for every `λ ∈ (0,1]`, `∫₀^∞ e^{-λt} p̄_t(0,0) dt ≤ 2048`. -/
theorem annealed_laplace_le_2048 {lambda : ℝ} (hlambda : 0 < lambda) (hlambda1 : lambda ≤ 1) :
    (∫⁻ t in Ici (0:ℝ), ENNReal.ofReal (Real.exp (-lambda * t)) *
        Manhattan.annealedContinuousKernel t 0 0) ≤ ENNReal.ofReal 2048 := by
  rw [Manhattan.Glue.concreteGreenIdentity lambda hlambda]
  exact ENNReal.ofReal_le_ofReal (normalizedGreenIntegral_le_2048 hlambda hlambda1)

/-- **`eq:green-explicit`** (`paper/arxiv/main.tex:1118-1120`):
`∫₀^∞ p̄_t(0,0) dt ≤ 2048`. -/
theorem annealed_green_le_2048 :
    (∫⁻ t in Ici (0:ℝ), Manhattan.annealedContinuousKernel t 0 0) ≤ ENNReal.ofReal 2048 :=
  Constant.undamped_le_of_uniform_damped _ fun _ hl hl1 => annealed_laplace_le_2048 hl hl1

end

end Manhattan.Paper
