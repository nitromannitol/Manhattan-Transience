import Manhattan.Glue.SummandThree

/-!
# The two-row `(h,h)` sector of summand 3 of (22)

`Manhattan.Glue.summandThreeBound_of_sector_bounds` reduces summand 3 of (22)
to one bound per degree-two sector.  This file proves the two-row half,
`Manhattan.Glue.summandThreeTwoRowSectorBound`, with the explicit constant
`Manhattan.Glue.twoRowSummandConstant`.

## What has to happen

By `Manhattan.Glue.type11WalshAnalysis_concreteFiberA_add` the `(h,h)` sector
of the residual is `(D₁f_p)₁₁` alone, and by
`Manhattan.Glue.inv_symbolWeight_type11Pattern` its dual energy is the
integral of `Manhattan.Estimates.twoRowHMinusWeight q p₁ (p₂+s+s')` against
the squared modulus of `Manhattan.Glue.type11FreqFun` of those coefficients.
Bounding the weight pointwise by `(λ+d(p₁))⁻¹` and using that
`type11FreqFun` is an isometry gives `≍ |p₁|²/(Kδ(|p₁|)³)`, which is
unbounded.  The gain has to come from the `α`-average of the weight, which is
what Lemma 4.1(d) supplies.

## How it is extracted

`Manhattan.Glue.type11RawIndex` is the *sorted* pair, so the coefficient
`(D₁f_p)₁₁` at the raw index `(m,m')`, `m<m'`, vanishes unless one of the two
row indices is the origin row.  Hence the raw coefficients split along the
two one-variable slices `Manhattan.Glue.sliceOne` and
`Manhattan.Glue.sliceZero` of `ℤ²`
(`Manhattan.Glue.type11RawExtend_twoRowRaiseCoeff`), and the frequency
function is the sum of two pullbacks of one-variable `L²` functions
(`Manhattan.Glue.type11FreqFun_twoRowRaiseCoeff`).

On a one-variable slice the two-row weight decouples: the missing angle is a
full period of a `2π`-periodic function, so its integral is the `α`-average
`Manhattan.Glue.twoRowWeightAverage` whatever the other angle is
(`Manhattan.Glue.integral_angleWeight_slice`).  Fubini then gives
`Manhattan.Glue.integral_twoRowAngleWeight_rowLiftOne` and its mirror: the
weighted energy of a pullback is the average times the squared `L²` norm.
This is the block diagonality in `m-m'`, in the only form the bound needs.

The same average is what Lemma 4.1(d) controls: the degree-one coefficient
`Manhattan.Estimates.degreeOneCoefficient` is purely imaginary with a fixed
sign on its support (`Manhattan.Glue.degreeOneCoefficient_inner_nonneg`), so
the symmetrized two-row residual dominates the half carried by the first row
frequency, and that half integrates to the average times the squared
degree-one mass (`Manhattan.Glue.twoRowWeightAverage_mul_degreeOne_le`).

Paper: `eq:D2a` = (27) (`manuscript.tex:829`), `lem:onecoin` = Lemma 4.1(d)
(`manuscript.tex:907-958`), and `lem:correction-calculation` = Lemma 5.4
(`manuscript.tex:1305`).
-/

open MeasureTheory Set UnitAddTorus
open scoped ENNReal

namespace Manhattan.Glue

noncomputable section

/-! ## ℓ² helpers -/

theorem memlp_two_of_norm_le {ι : Type*} {f g : ι → ℂ} (hg : Memℓp g 2)
    (h : ∀ i, ‖f i‖ ≤ ‖g i‖) : Memℓp f 2 := by
  have hgs : Summable fun i => ‖g i‖ ^ (2 : ℝ≥0∞).toReal :=
    (memℓp_gen_iff (by norm_num)).1 hg
  refine memℓp_gen (hgs.of_nonneg_of_le (fun i => by positivity) (fun i => ?_))
  exact Real.rpow_le_rpow (norm_nonneg _) (h i) (by norm_num)

theorem lp_norm_le_of_apply_le {ι κ : Type*} (a : ℓ²(ι, ℂ)) (b : ℓ²(κ, ℂ))
    (j : ι → κ) (hj : Function.Injective j) (h : ∀ i, ‖a i‖ ≤ ‖b (j i)‖) :
    ‖a‖ ≤ ‖b‖ := by
  have ha := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) a
  have hb := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) b
  have hsum : ∑' i : ι, ‖a i‖ ^ (2 : ℝ≥0∞).toReal
      ≤ ∑' k : κ, ‖b k‖ ^ (2 : ℝ≥0∞).toReal :=
    Summable.tsum_le_tsum_of_inj j hj (fun k _ => by positivity)
      (fun i => Real.rpow_le_rpow (norm_nonneg _) (h i) (by norm_num))
      ((memℓp_gen_iff (by norm_num)).1 (lp.memℓp a))
      ((memℓp_gen_iff (by norm_num)).1 (lp.memℓp b))
  rw [← ha, ← hb] at hsum
  by_contra hcon
  push_neg at hcon
  have hlt := Real.rpow_lt_rpow (norm_nonneg b) hcon
    (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
  linarith

/-! ## The two-row weight on the frequency torus -/

/-- The reciprocal two-row symbol, as a function of the two line angles. -/
def twoRowAngleWeight (q : Estimates.Parameters) (p₁ p₂ : ℝ)
    (t : UnitAddTorus (Fin 2)) : ℝ :=
  Estimates.twoRowHMinusWeight q p₁
    (p₂ + Manhattan.unitTorusAngle (t 0) + Manhattan.unitTorusAngle (t 1))

/-- The `α`-average of the two-row weight over the normalized torus. -/
def twoRowWeightAverage (q : Estimates.Parameters) (p₁ : ℝ) : ℝ :=
  Estimates.torusIntegral (Estimates.twoRowHMinusWeight q p₁)

theorem twoRowHMinusWeight_periodic (q : Estimates.Parameters) (p₁ : ℝ) :
    Function.Periodic (Estimates.twoRowHMinusWeight q p₁) (2 * Real.pi) := by
  intro alpha
  unfold Estimates.twoRowHMinusWeight
  rw [dispersion_periodic alpha]

theorem twoRowHMinusWeight_nonneg {q : Estimates.Parameters} (hlam : 0 < q.lambda)
    (p₁ alpha : ℝ) : 0 ≤ Estimates.twoRowHMinusWeight q p₁ alpha := by
  unfold Estimates.twoRowHMinusWeight
  have h1 := Estimates.dispersion_nonneg p₁
  have h2 := Estimates.dispersion_nonneg alpha
  positivity

theorem twoRowHMinusWeight_le {q : Estimates.Parameters} (hlam : 0 < q.lambda)
    (p₁ alpha : ℝ) : Estimates.twoRowHMinusWeight q p₁ alpha ≤ q.lambda⁻¹ := by
  unfold Estimates.twoRowHMinusWeight
  have h1 := Estimates.dispersion_nonneg p₁
  have h2 := Estimates.dispersion_nonneg alpha
  exact (inv_le_inv₀ (by linarith) hlam).2 (by linarith)

theorem measurable_twoRowHMinusWeight (q : Estimates.Parameters) (p₁ : ℝ) :
    Measurable (Estimates.twoRowHMinusWeight q p₁) := by
  unfold Estimates.twoRowHMinusWeight Estimates.dispersion
  fun_prop

theorem measurable_twoRowAngleWeight (q : Estimates.Parameters) (p₁ p₂ : ℝ) :
    Measurable (twoRowAngleWeight q p₁ p₂) := by
  refine (measurable_twoRowHMinusWeight q p₁).comp ?_
  exact ((measurable_const.add
    (Manhattan.unitTorusAngle_measurable.comp (measurable_pi_apply 0))).add
    (Manhattan.unitTorusAngle_measurable.comp (measurable_pi_apply 1)))

theorem twoRowAngleWeight_nonneg {q : Estimates.Parameters} (hlam : 0 < q.lambda)
    (p₁ p₂ : ℝ) (t : UnitAddTorus (Fin 2)) : 0 ≤ twoRowAngleWeight q p₁ p₂ t :=
  twoRowHMinusWeight_nonneg hlam _ _

theorem twoRowAngleWeight_le {q : Estimates.Parameters} (hlam : 0 < q.lambda)
    (p₁ p₂ : ℝ) (t : UnitAddTorus (Fin 2)) :
    twoRowAngleWeight q p₁ p₂ t ≤ q.lambda⁻¹ :=
  twoRowHMinusWeight_le hlam _ _

theorem twoRowWeightAverage_nonneg {q : Estimates.Parameters} (hlam : 0 < q.lambda)
    (p₁ : ℝ) : 0 ≤ twoRowWeightAverage q p₁ :=
  torusIntegral_nonneg (fun alpha => twoRowHMinusWeight_nonneg hlam p₁ alpha)

/-- The `t₀`-average of the two-row weight is the `α`-average, for every
fixed value of the remaining angle. -/
theorem integral_angleWeight_slice (q : Estimates.Parameters) (p₁ p₂ c : ℝ) :
    (∫ x : UnitAddCircle, Estimates.twoRowHMinusWeight q p₁
        (p₂ + Manhattan.unitTorusAngle x + c) ∂AddCircle.haarAddCircle)
      = twoRowWeightAverage q p₁ := by
  have h := integral_haarAddCircle_angle
    (fun s : ℝ => Estimates.twoRowHMinusWeight q p₁ (p₂ + s + c))
  rw [h, twoRowWeightAverage]
  have hfun : (fun s : ℝ => Estimates.twoRowHMinusWeight q p₁ (p₂ + s + c))
      = fun s : ℝ => Estimates.twoRowHMinusWeight q p₁ (s + (p₂ + c)) := by
    funext s; ring_nf
  rw [hfun]
  exact torusIntegral_comp_add_right (twoRowHMinusWeight_periodic q p₁) (p₂ + c)

theorem integral_angleWeight_slice' (q : Estimates.Parameters) (p₁ p₂ c : ℝ) :
    (∫ x : UnitAddCircle, Estimates.twoRowHMinusWeight q p₁
        (p₂ + c + Manhattan.unitTorusAngle x) ∂AddCircle.haarAddCircle)
      = twoRowWeightAverage q p₁ := by
  have h := integral_angleWeight_slice q p₁ p₂ c
  refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)) h
  ring_nf

/-! ## The two one-variable slices of the two-row frequency torus -/

/-- The two-row raw index of a coefficient carried by the origin row in the
first coordinate. -/
def sliceOne (k : ℤ) : Fin 2 → ℤ := ![0, k]

/-- The two-row raw index of a coefficient carried by the origin row in the
second coordinate. -/
def sliceZero (k : ℤ) : Fin 2 → ℤ := ![k, 0]

theorem sliceOne_injective : Function.Injective sliceOne := by
  intro k l h
  simpa [sliceOne] using congrFun h 1

theorem sliceZero_injective : Function.Injective sliceZero := by
  intro k l h
  simpa [sliceZero] using congrFun h 0

theorem measurePreserving_evalOne :
    MeasurePreserving (fun t : UnitAddTorus (Fin 2) => t 1)
      (LineTorusMeasure 2) (AddCircle.haarAddCircle : Measure UnitAddCircle) :=
  MeasureTheory.measurePreserving_eval (μ := fun _ : Fin 2 =>
    (AddCircle.haarAddCircle : Measure UnitAddCircle)) 1

theorem measurePreserving_evalZero :
    MeasurePreserving (fun t : UnitAddTorus (Fin 2) => t 0)
      (LineTorusMeasure 2) (AddCircle.haarAddCircle : Measure UnitAddCircle) :=
  MeasureTheory.measurePreserving_eval (μ := fun _ : Fin 2 =>
    (AddCircle.haarAddCircle : Measure UnitAddCircle)) 0

/-- Pullback of a one-variable `L²` function along the second line angle. -/
def rowLiftOne :
    Lp ℂ 2 (AddCircle.haarAddCircle : Measure UnitAddCircle) →ₗᵢ[ℂ]
      Lp ℂ 2 (LineTorusMeasure 2) :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun t : UnitAddTorus (Fin 2) => t 1)
    measurePreserving_evalOne

/-- Pullback of a one-variable `L²` function along the first line angle. -/
def rowLiftZero :
    Lp ℂ 2 (AddCircle.haarAddCircle : Measure UnitAddCircle) →ₗᵢ[ℂ]
      Lp ℂ 2 (LineTorusMeasure 2) :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun t : UnitAddTorus (Fin 2) => t 0)
    measurePreserving_evalZero

theorem mFourierLp_sliceOne (k : ℤ) :
    (mFourierLp 2 (sliceOne k) : Lp ℂ 2 (LineTorusMeasure 2))
      = rowLiftOne (fourierLp (T := 1) 2 k) := by
  refine MeasureTheory.Lp.ext ?_
  have h1 := coeFn_mFourierLp (d := Fin 2) 2 (sliceOne k)
  have h2 : (rowLiftOne (fourierLp (T := 1) 2 k) : UnitAddTorus (Fin 2) → ℂ)
      =ᵐ[LineTorusMeasure 2]
        ((fourierLp (T := 1) 2 k : UnitAddCircle → ℂ) ∘ fun t : UnitAddTorus (Fin 2) => t 1) :=
    Lp.coeFn_compMeasurePreserving _ measurePreserving_evalOne
  have h3 : ((fourierLp (T := 1) 2 k : UnitAddCircle → ℂ) ∘ fun t : UnitAddTorus (Fin 2) => t 1)
      =ᵐ[LineTorusMeasure 2] (fun t : UnitAddTorus (Fin 2) => fourier k (t 1)) :=
    measurePreserving_evalOne.quasiMeasurePreserving.ae_eq_comp
      (coeFn_fourierLp (T := 1) 2 k)
  filter_upwards [h1, h2, h3] with t ht1 ht2 ht3
  rw [ht1, ht2, ht3, mFourier]
  simp [sliceOne, Fin.prod_univ_two]

theorem mFourierLp_sliceZero (k : ℤ) :
    (mFourierLp 2 (sliceZero k) : Lp ℂ 2 (LineTorusMeasure 2))
      = rowLiftZero (fourierLp (T := 1) 2 k) := by
  refine MeasureTheory.Lp.ext ?_
  have h1 := coeFn_mFourierLp (d := Fin 2) 2 (sliceZero k)
  have h2 : (rowLiftZero (fourierLp (T := 1) 2 k) : UnitAddTorus (Fin 2) → ℂ)
      =ᵐ[LineTorusMeasure 2]
        ((fourierLp (T := 1) 2 k : UnitAddCircle → ℂ) ∘ fun t : UnitAddTorus (Fin 2) => t 0) :=
    Lp.coeFn_compMeasurePreserving _ measurePreserving_evalZero
  have h3 : ((fourierLp (T := 1) 2 k : UnitAddCircle → ℂ) ∘ fun t : UnitAddTorus (Fin 2) => t 0)
      =ᵐ[LineTorusMeasure 2] (fun t : UnitAddTorus (Fin 2) => fourier k (t 0)) :=
    measurePreserving_evalZero.quasiMeasurePreserving.ae_eq_comp
      (coeFn_fourierLp (T := 1) 2 k)
  filter_upwards [h1, h2, h3] with t ht1 ht2 ht3
  rw [ht1, ht2, ht3, mFourier]
  simp [sliceZero, Fin.prod_univ_two]

/-- A two-dimensional `L²` function whose Fourier support is the first slice
is the pullback of a one-variable function. -/
theorem freqSliceOne (a : ℓ²(ℤ, ℂ)) :
    (mFourierBasis (d := Fin 2)).repr.symm (l2Extend sliceOne sliceOne_injective a)
      = rowLiftOne ((fourierBasis (T := 1)).repr.symm a) := by
  refine l2_ext'
    (((mFourierBasis (d := Fin 2)).repr.symm.toLinearIsometry.comp
        (l2Extend sliceOne sliceOne_injective)).toContinuousLinearMap)
    ((rowLiftOne.comp (fourierBasis (T := 1)).repr.symm.toLinearIsometry).toContinuousLinearMap)
    ?_ a
  intro k
  show (mFourierBasis (d := Fin 2)).repr.symm
      (l2Extend sliceOne sliceOne_injective (lp.single 2 k (1 : ℂ)))
    = rowLiftOne ((fourierBasis (T := 1)).repr.symm (lp.single 2 k (1 : ℂ)))
  rw [l2Extend_single, HilbertBasis.repr_symm_single, HilbertBasis.repr_symm_single,
    coe_mFourierBasis, coe_fourierBasis]
  exact mFourierLp_sliceOne k

theorem freqSliceZero (a : ℓ²(ℤ, ℂ)) :
    (mFourierBasis (d := Fin 2)).repr.symm (l2Extend sliceZero sliceZero_injective a)
      = rowLiftZero ((fourierBasis (T := 1)).repr.symm a) := by
  refine l2_ext'
    (((mFourierBasis (d := Fin 2)).repr.symm.toLinearIsometry.comp
        (l2Extend sliceZero sliceZero_injective)).toContinuousLinearMap)
    ((rowLiftZero.comp (fourierBasis (T := 1)).repr.symm.toLinearIsometry).toContinuousLinearMap)
    ?_ a
  intro k
  show (mFourierBasis (d := Fin 2)).repr.symm
      (l2Extend sliceZero sliceZero_injective (lp.single 2 k (1 : ℂ)))
    = rowLiftZero ((fourierBasis (T := 1)).repr.symm (lp.single 2 k (1 : ℂ)))
  rw [l2Extend_single, HilbertBasis.repr_symm_single, HilbertBasis.repr_symm_single,
    coe_mFourierBasis, coe_fourierBasis]
  exact mFourierLp_sliceZero k

/-! ## The block-diagonal gain: the weight decouples on a one-variable slice -/

/-- **The `α`-average is the whole gain.**  On the slice carried by the second
line angle the two-row weight integrates out to its `α`-average, so the
weighted energy of a pullback is the average times the squared `L²` norm. -/
theorem integral_twoRowAngleWeight_rowLiftOne {q : Estimates.Parameters}
    (hlam : 0 < q.lambda) (p₁ p₂ : ℝ)
    (h : Lp ℂ 2 (AddCircle.haarAddCircle : Measure UnitAddCircle)) :
    (∫ t, twoRowAngleWeight q p₁ p₂ t *
        ‖(rowLiftOne h : UnitAddTorus (Fin 2) → ℂ) t‖ ^ 2 ∂(LineTorusMeasure 2))
      = twoRowWeightAverage q p₁ * ‖h‖ ^ 2 := by
  classical
  set G : UnitAddCircle × UnitAddCircle → ℝ := fun z =>
    Estimates.twoRowHMinusWeight q p₁
        (p₂ + Manhattan.unitTorusAngle z.1 + Manhattan.unitTorusAngle z.2) *
      ‖(h : UnitAddCircle → ℂ) z.2‖ ^ 2 with hG
  have hcoe : (rowLiftOne h : UnitAddTorus (Fin 2) → ℂ) =ᵐ[LineTorusMeasure 2]
      ((h : UnitAddCircle → ℂ) ∘ fun t : UnitAddTorus (Fin 2) => t 1) :=
    Lp.coeFn_compMeasurePreserving _ measurePreserving_evalOne
  have hstep1 : (∫ t, twoRowAngleWeight q p₁ p₂ t *
        ‖(rowLiftOne h : UnitAddTorus (Fin 2) → ℂ) t‖ ^ 2 ∂(LineTorusMeasure 2))
      = ∫ t, G (t 0, t 1) ∂(LineTorusMeasure 2) := by
    refine integral_congr_ae ?_
    filter_upwards [hcoe] with t ht
    rw [ht, hG, twoRowAngleWeight]
    rfl
  have hmp := MeasureTheory.measurePreserving_piFinTwo
    (μ := fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle))
  have hstep2 : (∫ t, G (t 0, t 1) ∂(LineTorusMeasure 2))
      = ∫ z, G z ∂((AddCircle.haarAddCircle : Measure UnitAddCircle).prod
          (AddCircle.haarAddCircle : Measure UnitAddCircle)) := hmp.integral_comp' G
  have hsq : Integrable (fun a : UnitAddCircle => ‖(h : UnitAddCircle → ℂ) a‖ ^ 2)
      AddCircle.haarAddCircle := by
    have := (Lp.memLp h).integrable_norm_rpow (by norm_num) (by norm_num)
    simpa using this
  have hGint : Integrable G ((AddCircle.haarAddCircle : Measure UnitAddCircle).prod
      (AddCircle.haarAddCircle : Measure UnitAddCircle)) := by
    have hdom : Integrable
        (fun z : UnitAddCircle × UnitAddCircle =>
          q.lambda⁻¹ * ‖(h : UnitAddCircle → ℂ) z.2‖ ^ 2)
        ((AddCircle.haarAddCircle : Measure UnitAddCircle).prod
          (AddCircle.haarAddCircle : Measure UnitAddCircle)) :=
      (hsq.const_mul _).comp_snd _
    have hmeas : AEStronglyMeasurable G
        ((AddCircle.haarAddCircle : Measure UnitAddCircle).prod
          (AddCircle.haarAddCircle : Measure UnitAddCircle)) := by
      have h1 : Measurable fun z : UnitAddCircle × UnitAddCircle =>
          Estimates.twoRowHMinusWeight q p₁
            (p₂ + Manhattan.unitTorusAngle z.1 + Manhattan.unitTorusAngle z.2) := by
        refine (measurable_twoRowHMinusWeight q p₁).comp ?_
        exact ((measurable_const.add
          (Manhattan.unitTorusAngle_measurable.comp measurable_fst)).add
          (Manhattan.unitTorusAngle_measurable.comp measurable_snd))
      exact h1.aestronglyMeasurable.mul
        (((Lp.aestronglyMeasurable h).norm.pow 2).comp_snd)
    refine hdom.mono' hmeas ?_
    filter_upwards with z
    rw [hG]
    dsimp only
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (twoRowHMinusWeight_nonneg hlam _ _) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_right (twoRowHMinusWeight_le hlam _ _) (sq_nonneg _)
  rw [hstep1, hstep2, integral_prod_symm G hGint]
  have hinner : ∀ y : UnitAddCircle,
      (∫ x : UnitAddCircle, G (x, y) ∂AddCircle.haarAddCircle)
        = twoRowWeightAverage q p₁ * ‖(h : UnitAddCircle → ℂ) y‖ ^ 2 := by
    intro y
    rw [hG]
    dsimp only
    rw [integral_mul_const, integral_angleWeight_slice]
  rw [integral_congr_ae (Filter.Eventually.of_forall hinner), integral_const_mul,
    integral_norm_sq_lp]

/-- The same statement on the slice carried by the first line angle. -/
theorem integral_twoRowAngleWeight_rowLiftZero {q : Estimates.Parameters}
    (hlam : 0 < q.lambda) (p₁ p₂ : ℝ)
    (h : Lp ℂ 2 (AddCircle.haarAddCircle : Measure UnitAddCircle)) :
    (∫ t, twoRowAngleWeight q p₁ p₂ t *
        ‖(rowLiftZero h : UnitAddTorus (Fin 2) → ℂ) t‖ ^ 2 ∂(LineTorusMeasure 2))
      = twoRowWeightAverage q p₁ * ‖h‖ ^ 2 := by
  classical
  set G : UnitAddCircle × UnitAddCircle → ℝ := fun z =>
    Estimates.twoRowHMinusWeight q p₁
        (p₂ + Manhattan.unitTorusAngle z.1 + Manhattan.unitTorusAngle z.2) *
      ‖(h : UnitAddCircle → ℂ) z.1‖ ^ 2 with hG
  have hcoe : (rowLiftZero h : UnitAddTorus (Fin 2) → ℂ) =ᵐ[LineTorusMeasure 2]
      ((h : UnitAddCircle → ℂ) ∘ fun t : UnitAddTorus (Fin 2) => t 0) :=
    Lp.coeFn_compMeasurePreserving _ measurePreserving_evalZero
  have hstep1 : (∫ t, twoRowAngleWeight q p₁ p₂ t *
        ‖(rowLiftZero h : UnitAddTorus (Fin 2) → ℂ) t‖ ^ 2 ∂(LineTorusMeasure 2))
      = ∫ t, G (t 0, t 1) ∂(LineTorusMeasure 2) := by
    refine integral_congr_ae ?_
    filter_upwards [hcoe] with t ht
    rw [ht, hG, twoRowAngleWeight]
    rfl
  have hmp := MeasureTheory.measurePreserving_piFinTwo
    (μ := fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure UnitAddCircle))
  have hstep2 : (∫ t, G (t 0, t 1) ∂(LineTorusMeasure 2))
      = ∫ z, G z ∂((AddCircle.haarAddCircle : Measure UnitAddCircle).prod
          (AddCircle.haarAddCircle : Measure UnitAddCircle)) := hmp.integral_comp' G
  have hsq : Integrable (fun a : UnitAddCircle => ‖(h : UnitAddCircle → ℂ) a‖ ^ 2)
      AddCircle.haarAddCircle := by
    have := (Lp.memLp h).integrable_norm_rpow (by norm_num) (by norm_num)
    simpa using this
  have hGint : Integrable G ((AddCircle.haarAddCircle : Measure UnitAddCircle).prod
      (AddCircle.haarAddCircle : Measure UnitAddCircle)) := by
    have hdom : Integrable
        (fun z : UnitAddCircle × UnitAddCircle =>
          q.lambda⁻¹ * ‖(h : UnitAddCircle → ℂ) z.1‖ ^ 2)
        ((AddCircle.haarAddCircle : Measure UnitAddCircle).prod
          (AddCircle.haarAddCircle : Measure UnitAddCircle)) :=
      (hsq.const_mul _).comp_fst _
    have hmeas : AEStronglyMeasurable G
        ((AddCircle.haarAddCircle : Measure UnitAddCircle).prod
          (AddCircle.haarAddCircle : Measure UnitAddCircle)) := by
      have h1 : Measurable fun z : UnitAddCircle × UnitAddCircle =>
          Estimates.twoRowHMinusWeight q p₁
            (p₂ + Manhattan.unitTorusAngle z.1 + Manhattan.unitTorusAngle z.2) := by
        refine (measurable_twoRowHMinusWeight q p₁).comp ?_
        exact ((measurable_const.add
          (Manhattan.unitTorusAngle_measurable.comp measurable_fst)).add
          (Manhattan.unitTorusAngle_measurable.comp measurable_snd))
      exact h1.aestronglyMeasurable.mul
        (((Lp.aestronglyMeasurable h).norm.pow 2).comp_fst)
    refine hdom.mono' hmeas ?_
    filter_upwards with z
    rw [hG]
    dsimp only
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (twoRowHMinusWeight_nonneg hlam _ _) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_right (twoRowHMinusWeight_le hlam _ _) (sq_nonneg _)
  rw [hstep1, hstep2, integral_prod G hGint]
  have hinner : ∀ x : UnitAddCircle,
      (∫ y : UnitAddCircle, G (x, y) ∂AddCircle.haarAddCircle)
        = twoRowWeightAverage q p₁ * ‖(h : UnitAddCircle → ℂ) x‖ ^ 2 := by
    intro x
    rw [hG]
    dsimp only
    rw [integral_mul_const, integral_angleWeight_slice']
  rw [integral_congr_ae (Filter.Eventually.of_forall hinner), integral_const_mul,
    integral_norm_sq_lp]

/-! ## The two-row coefficient vector of the raised competitor -/

theorem l2Extend_sliceOne_apply (a : ℓ²(ℤ, ℂ)) (n : Fin 2 → ℤ) :
    l2Extend sliceOne sliceOne_injective a n = if n 0 = 0 then a (n 1) else 0 := by
  classical
  by_cases h : n 0 = 0
  · have hn : sliceOne (n 1) = n := by
      funext i
      fin_cases i
      · simpa [sliceOne] using h.symm
      · simp [sliceOne]
    rw [if_pos h, ← hn, l2Extend_apply]
    simp [sliceOne]
  · rw [if_neg h]
    refine l2Extend_apply_eq_zero _ _ _ (fun k hk => h ?_)
    have := congrFun hk 0
    simpa [sliceOne] using this.symm

theorem l2Extend_sliceZero_apply (a : ℓ²(ℤ, ℂ)) (n : Fin 2 → ℤ) :
    l2Extend sliceZero sliceZero_injective a n = if n 1 = 0 then a (n 0) else 0 := by
  classical
  by_cases h : n 1 = 0
  · have hn : sliceZero (n 0) = n := by
      funext i
      fin_cases i
      · simp [sliceZero]
      · simpa [sliceZero] using h.symm
    rw [if_pos h, ← hn, l2Extend_apply]
    simp [sliceZero]
  · rw [if_neg h]
    refine l2Extend_apply_eq_zero _ _ _ (fun k hk => h ?_)
    have := congrFun hk 1
    simpa [sliceZero] using this.symm

theorem type11RawIndex_orderedType11Equiv (n : Fin 2 → ℤ) (h : n 0 < n 1) :
    type11RawIndex (orderedType11Equiv ⟨n, h⟩) = n := by
  rw [type11RawIndex, Equiv.symm_apply_apply]

/-- The two-row degree-two Walsh coefficients of `D₁f_p`. -/
def twoRowRaiseCoeff (p : Fin 2 → ℝ) (c : Manhattan.RowLineCoefficient) :
    ℓ²(Manhattan.Type11Index, ℂ) :=
  Manhattan.type11WalshAnalysis
    (walshRaise p (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal c))

theorem twoRowRaiseCoeff_apply (p : Fin 2 → ℝ) (c : Manhattan.RowLineCoefficient)
    (S : Manhattan.Type11Index) :
    twoRowRaiseCoeff p c S =
      (if type11RawIndex S 0 = 0 then
        Complex.I * (Real.sin (p 0) : ℂ) * c (type11RawIndex S 1) else 0) +
      (if type11RawIndex S 1 = 0 then
        Complex.I * (Real.sin (p 0) : ℂ) * c (type11RawIndex S 0) else 0) := by
  have hne := type11RawIndex_ne S
  have h := type11WalshAnalysis_walshRaise_rowPair p c hne
  have hS : (⟨rowPairFinset (type11RawIndex S 0, type11RawIndex S 1),
      isType11Index_rowPairFinset hne⟩ : Manhattan.Type11Index) = S :=
    Subtype.ext (rowPairFinset_type11RawIndex S)
  rw [hS] at h
  exact h

theorem memlp_scaled_row (p : Fin 2 → ℝ) (c : Manhattan.RowLineCoefficient) :
    Memℓp (fun k : ℤ => Complex.I * (Real.sin (p 0) : ℂ) * c k) 2 := by
  have h := lp.memℓp ((Complex.I * (Real.sin (p 0) : ℂ)) • c)
  simpa using h

/-- The positive-frequency half of the two-row coefficient vector, read on the
first slice. -/
def sliceOneCoeff (p : Fin 2 → ℝ) (c : Manhattan.RowLineCoefficient) : ℓ²(ℤ, ℂ) :=
  ⟨fun k => if 0 < k then Complex.I * (Real.sin (p 0) : ℂ) * c k else 0, by
    refine memlp_two_of_norm_le (memlp_scaled_row p c) (fun k => ?_)
    by_cases h : 0 < k
    · rw [if_pos h]
    · rw [if_neg h, norm_zero]
      positivity⟩

/-- The negative-frequency half, read on the second slice. -/
def sliceZeroCoeff (p : Fin 2 → ℝ) (c : Manhattan.RowLineCoefficient) : ℓ²(ℤ, ℂ) :=
  ⟨fun k => if k < 0 then Complex.I * (Real.sin (p 0) : ℂ) * c k else 0, by
    refine memlp_two_of_norm_le (memlp_scaled_row p c) (fun k => ?_)
    by_cases h : k < 0
    · rw [if_pos h]
    · rw [if_neg h, norm_zero]
      positivity⟩

@[simp] theorem sliceOneCoeff_apply (p : Fin 2 → ℝ) (c : Manhattan.RowLineCoefficient)
    (k : ℤ) :
    sliceOneCoeff p c k = if 0 < k then Complex.I * (Real.sin (p 0) : ℂ) * c k else 0 := rfl

@[simp] theorem sliceZeroCoeff_apply (p : Fin 2 → ℝ) (c : Manhattan.RowLineCoefficient)
    (k : ℤ) :
    sliceZeroCoeff p c k = if k < 0 then Complex.I * (Real.sin (p 0) : ℂ) * c k else 0 := rfl

/-- **The two-row sector splits along the two one-variable slices.**  The raw
two-row coefficients of `D₁f_p` are carried by the two lines through the
origin row, and the sorted convention puts the two halves on the two
slices. -/
theorem type11RawExtend_twoRowRaiseCoeff (p : Fin 2 → ℝ)
    (c : Manhattan.RowLineCoefficient) :
    type11RawExtend (twoRowRaiseCoeff p c)
      = l2Extend sliceOne sliceOne_injective (sliceOneCoeff p c)
        + l2Extend sliceZero sliceZero_injective (sliceZeroCoeff p c) := by
  classical
  apply lp.ext
  funext n
  have hsum : ((l2Extend sliceOne sliceOne_injective (sliceOneCoeff p c)
        + l2Extend sliceZero sliceZero_injective (sliceZeroCoeff p c) :
          ℓ²(Fin 2 → ℤ, ℂ)) : (Fin 2 → ℤ) → ℂ) n
      = l2Extend sliceOne sliceOne_injective (sliceOneCoeff p c) n
        + l2Extend sliceZero sliceZero_injective (sliceZeroCoeff p c) n := rfl
  rw [hsum, l2Extend_sliceOne_apply, l2Extend_sliceZero_apply]
  by_cases hex : n 0 < n 1
  · set S : Manhattan.Type11Index := orderedType11Equiv ⟨n, hex⟩ with hS
    have hraw : type11RawIndex S = n := type11RawIndex_orderedType11Equiv n hex
    have hleft : type11RawExtend (twoRowRaiseCoeff p c) n = twoRowRaiseCoeff p c S := by
      rw [type11RawExtend, ← hraw, l2Extend_apply]
    rw [hleft, twoRowRaiseCoeff_apply, hraw]
    by_cases h0 : n 0 = 0
    · have h1 : n 1 ≠ 0 := by omega
      have h1pos : 0 < n 1 := by omega
      rw [if_pos h0, if_neg h1, if_pos h0, if_neg h1, sliceOneCoeff_apply, if_pos h1pos]
    · by_cases h1 : n 1 = 0
      · have h0neg : n 0 < 0 := by omega
        rw [if_neg h0, if_pos h1, if_neg h0, if_pos h1, sliceZeroCoeff_apply,
          if_pos h0neg]
      · rw [if_neg h0, if_neg h1, if_neg h0, if_neg h1]
  · have hleft : type11RawExtend (twoRowRaiseCoeff p c) n = 0 := by
      refine l2Extend_apply_eq_zero _ _ _ (fun S hS => ?_)
      exact absurd (hS ▸ type11RawIndex_lt S) hex
    rw [hleft]
    by_cases h0 : n 0 = 0
    · have h1 : ¬ (0 < n 1) := by omega
      rw [if_pos h0, sliceOneCoeff_apply, if_neg h1]
      by_cases h1z : n 1 = 0
      · rw [if_pos h1z, sliceZeroCoeff_apply, h0, if_neg (by omega : ¬ ((0 : ℤ) < 0))]
        ring
      · rw [if_neg h1z]
        ring
    · rw [if_neg h0]
      by_cases h1z : n 1 = 0
      · have h0pos : ¬ (n 0 < 0) := by omega
        rw [if_pos h1z, sliceZeroCoeff_apply, if_neg h0pos]
        ring
      · rw [if_neg h1z]
        ring

/-- **The two-row frequency function is a sum of two one-variable pullbacks.** -/
theorem type11FreqFun_twoRowRaiseCoeff (p : Fin 2 → ℝ)
    (c : Manhattan.RowLineCoefficient) :
    type11FreqFun (twoRowRaiseCoeff p c)
      = rowLiftOne ((fourierBasis (T := 1)).repr.symm (sliceOneCoeff p c))
        + rowLiftZero ((fourierBasis (T := 1)).repr.symm (sliceZeroCoeff p c)) := by
  show (mFourierBasis (d := Fin 2)).repr.symm
      (type11RawExtend (twoRowRaiseCoeff p c)) = _
  rw [type11RawExtend_twoRowRaiseCoeff, map_add, freqSliceOne, freqSliceZero]

theorem norm_mul_I_sin (p : Fin 2 → ℝ) :
    ‖Complex.I * (Real.sin (p 0) : ℂ)‖ = |Real.sin (p 0)| := by
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]

theorem norm_sliceOneCoeff_le (p : Fin 2 → ℝ) (c : Manhattan.RowLineCoefficient) :
    ‖sliceOneCoeff p c‖ ≤ |Real.sin (p 0)| * ‖c‖ := by
  classical
  have hb : ‖((Complex.I * (Real.sin (p 0) : ℂ)) • c : ℓ²(ℤ, ℂ))‖
      = |Real.sin (p 0)| * ‖c‖ := by
    rw [norm_smul, norm_mul_I_sin]
  refine le_trans (lp_norm_le_of_apply_le (sliceOneCoeff p c)
    ((Complex.I * (Real.sin (p 0) : ℂ)) • c) id Function.injective_id (fun k => ?_)) hb.le
  have hval : (((Complex.I * (Real.sin (p 0) : ℂ)) • c : ℓ²(ℤ, ℂ)) : ℤ → ℂ) (id k)
      = Complex.I * (Real.sin (p 0) : ℂ) * c k := rfl
  rw [hval, sliceOneCoeff_apply]
  by_cases h : 0 < k
  · rw [if_pos h]
  · rw [if_neg h, norm_zero]
    positivity

theorem norm_sliceZeroCoeff_le (p : Fin 2 → ℝ) (c : Manhattan.RowLineCoefficient) :
    ‖sliceZeroCoeff p c‖ ≤ |Real.sin (p 0)| * ‖c‖ := by
  classical
  have hb : ‖((Complex.I * (Real.sin (p 0) : ℂ)) • c : ℓ²(ℤ, ℂ))‖
      = |Real.sin (p 0)| * ‖c‖ := by
    rw [norm_smul, norm_mul_I_sin]
  refine le_trans (lp_norm_le_of_apply_le (sliceZeroCoeff p c)
    ((Complex.I * (Real.sin (p 0) : ℂ)) • c) id Function.injective_id (fun k => ?_)) hb.le
  have hval : (((Complex.I * (Real.sin (p 0) : ℂ)) • c : ℓ²(ℤ, ℂ)) : ℤ → ℂ) (id k)
      = Complex.I * (Real.sin (p 0) : ℂ) * c k := rfl
  rw [hval, sliceZeroCoeff_apply]
  by_cases h : k < 0
  · rw [if_pos h]
  · rw [if_neg h, norm_zero]
    positivity

theorem integrable_twoRowAngleWeight_mul_sq {q : Estimates.Parameters}
    (hlam : 0 < q.lambda) (p₁ p₂ : ℝ) (F : Lp ℂ 2 (LineTorusMeasure 2)) :
    Integrable (fun t => twoRowAngleWeight q p₁ p₂ t *
      ‖(F : UnitAddTorus (Fin 2) → ℂ) t‖ ^ 2) (LineTorusMeasure 2) := by
  have hsq : Integrable (fun t => ‖(F : UnitAddTorus (Fin 2) → ℂ) t‖ ^ 2)
      (LineTorusMeasure 2) := by
    have := (Lp.memLp F).integrable_norm_rpow (by norm_num) (by norm_num)
    simpa using this
  refine (hsq.const_mul q.lambda⁻¹).mono'
    ((measurable_twoRowAngleWeight q p₁ p₂).aestronglyMeasurable.mul
      ((Lp.aestronglyMeasurable F).norm.pow 2)) ?_
  filter_upwards with t
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (twoRowAngleWeight_nonneg hlam p₁ p₂ t) (sq_nonneg _))]
  exact mul_le_mul_of_nonneg_right (twoRowAngleWeight_le hlam p₁ p₂ t) (sq_nonneg _)

/-! ## The two-row sector bound -/

/-- **The two-row (`h,h`) sector energy of `D₁f_p`.**  Both slices see the
same `α`-average of the weight, so the energy is at most four times that
average against the squared degree-one mass.  This is the estimate that the
pointwise weight bound `(λ+d(p₁))⁻¹` cannot give. -/
theorem hMinusEnergy_twoRowRaiseCoeff_le {q : Estimates.Parameters}
    (hlam : 0 < q.lambda) (p : Fin 2 → ℝ) (c : Manhattan.RowLineCoefficient) :
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hlam
        (Manhattan.type11WalshSynthesis (twoRowRaiseCoeff p c))
      ≤ 4 * twoRowWeightAverage q (p 0) * (Real.sin (p 0) ^ 2 * ‖c‖ ^ 2) := by
  classical
  set A : Lp ℂ 2 (LineTorusMeasure 2) :=
    rowLiftOne ((fourierBasis (T := 1)).repr.symm (sliceOneCoeff p c)) with hA
  set B : Lp ℂ 2 (LineTorusMeasure 2) :=
    rowLiftZero ((fourierBasis (T := 1)).repr.symm (sliceZeroCoeff p c)) with hB
  have hPsi : type11FreqFun (twoRowRaiseCoeff p c) = A + B :=
    type11FreqFun_twoRowRaiseCoeff p c
  rw [hMinusEnergy_type11WalshSynthesis hlam p (twoRowRaiseCoeff p c)]
  have hint : (∫ t, (symbolWeight 2 q.lambda p type11Pattern t)⁻¹ *
        ‖(type11FreqFun (twoRowRaiseCoeff p c) : UnitAddTorus (Fin 2) → ℂ) t‖ ^ 2
        ∂(LineTorusMeasure 2))
      = ∫ t, twoRowAngleWeight q (p 0) (p 1) t *
          ‖((A + B : Lp ℂ 2 (LineTorusMeasure 2)) : UnitAddTorus (Fin 2) → ℂ) t‖ ^ 2
          ∂(LineTorusMeasure 2) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    dsimp only
    rw [inv_symbolWeight_type11Pattern, hPsi]
    rfl
  rw [hint]
  have hptw : ∀ᵐ t ∂(LineTorusMeasure 2),
      twoRowAngleWeight q (p 0) (p 1) t *
          ‖((A + B : Lp ℂ 2 (LineTorusMeasure 2)) : UnitAddTorus (Fin 2) → ℂ) t‖ ^ 2
        ≤ 2 * (twoRowAngleWeight q (p 0) (p 1) t *
            ‖(A : UnitAddTorus (Fin 2) → ℂ) t‖ ^ 2)
          + 2 * (twoRowAngleWeight q (p 0) (p 1) t *
            ‖(B : UnitAddTorus (Fin 2) → ℂ) t‖ ^ 2) := by
    filter_upwards [Lp.coeFn_add A B] with t ht
    rw [ht]
    simp only [Pi.add_apply]
    have htri : ‖(A : UnitAddTorus (Fin 2) → ℂ) t + (B : UnitAddTorus (Fin 2) → ℂ) t‖
        ≤ ‖(A : UnitAddTorus (Fin 2) → ℂ) t‖ + ‖(B : UnitAddTorus (Fin 2) → ℂ) t‖ :=
      norm_add_le _ _
    have hsq : ‖(A : UnitAddTorus (Fin 2) → ℂ) t + (B : UnitAddTorus (Fin 2) → ℂ) t‖ ^ 2
        ≤ 2 * ‖(A : UnitAddTorus (Fin 2) → ℂ) t‖ ^ 2
          + 2 * ‖(B : UnitAddTorus (Fin 2) → ℂ) t‖ ^ 2 := by
      nlinarith [norm_nonneg ((A : UnitAddTorus (Fin 2) → ℂ) t),
        norm_nonneg ((B : UnitAddTorus (Fin 2) → ℂ) t),
        sq_nonneg (‖(A : UnitAddTorus (Fin 2) → ℂ) t‖ -
          ‖(B : UnitAddTorus (Fin 2) → ℂ) t‖),
        norm_nonneg ((A : UnitAddTorus (Fin 2) → ℂ) t +
          (B : UnitAddTorus (Fin 2) → ℂ) t)]
    have hw := twoRowAngleWeight_nonneg hlam (p 0) (p 1) t
    calc twoRowAngleWeight q (p 0) (p 1) t *
          ‖(A : UnitAddTorus (Fin 2) → ℂ) t + (B : UnitAddTorus (Fin 2) → ℂ) t‖ ^ 2
        ≤ twoRowAngleWeight q (p 0) (p 1) t *
            (2 * ‖(A : UnitAddTorus (Fin 2) → ℂ) t‖ ^ 2
              + 2 * ‖(B : UnitAddTorus (Fin 2) → ℂ) t‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hsq hw
      _ = 2 * (twoRowAngleWeight q (p 0) (p 1) t *
            ‖(A : UnitAddTorus (Fin 2) → ℂ) t‖ ^ 2)
          + 2 * (twoRowAngleWeight q (p 0) (p 1) t *
            ‖(B : UnitAddTorus (Fin 2) → ℂ) t‖ ^ 2) := by ring
  have hIA := integrable_twoRowAngleWeight_mul_sq hlam (p 0) (p 1) A
  have hIB := integrable_twoRowAngleWeight_mul_sq hlam (p 0) (p 1) B
  have hIAB := integrable_twoRowAngleWeight_mul_sq hlam (p 0) (p 1)
    (A + B : Lp ℂ 2 (LineTorusMeasure 2))
  refine le_trans (integral_mono_ae hIAB ((hIA.const_mul 2).add (hIB.const_mul 2)) hptw) ?_
  simp only [Pi.add_apply]
  rw [integral_add (hIA.const_mul 2) (hIB.const_mul 2), integral_const_mul,
    integral_const_mul, hA, hB, integral_twoRowAngleWeight_rowLiftOne hlam,
    integral_twoRowAngleWeight_rowLiftZero hlam,
    LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map]
  have hRnonneg := twoRowWeightAverage_nonneg hlam (p 0)
  have hAle := norm_sliceOneCoeff_le p c
  have hBle := norm_sliceZeroCoeff_le p c
  have hsin : |Real.sin (p 0)| * ‖c‖ ≥ 0 := by positivity
  have hAsq : ‖sliceOneCoeff p c‖ ^ 2 ≤ Real.sin (p 0) ^ 2 * ‖c‖ ^ 2 := by
    have := mul_self_le_mul_self (norm_nonneg _) hAle
    nlinarith [sq_abs (Real.sin (p 0)), norm_nonneg (sliceOneCoeff p c), norm_nonneg c]
  have hBsq : ‖sliceZeroCoeff p c‖ ^ 2 ≤ Real.sin (p 0) ^ 2 * ‖c‖ ^ 2 := by
    have := mul_self_le_mul_self (norm_nonneg _) hBle
    nlinarith [sq_abs (Real.sin (p 0)), norm_nonneg (sliceZeroCoeff p c), norm_nonneg c]
  nlinarith [hRnonneg, hAsq, hBsq]

/-! ## Lemma 4.1(d) sees the same `α`-average -/

theorem norm_I_sin_mul_sq (s : ℝ) (z : ℂ) :
    ‖Complex.I * (s : ℂ) * z‖ ^ 2 = s ^ 2 * ‖z‖ ^ 2 := by
  rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, mul_pow, sq_abs]

theorem torusIntegral_weight_shift (q : Estimates.Parameters) (p₁ p₂ r K : ℝ) :
    Estimates.torusIntegral
        (fun r' => K * Estimates.twoRowHMinusWeight q p₁ (r + r' - p₂))
      = K * twoRowWeightAverage q p₁ := by
  have hfun : (fun r' => K * Estimates.twoRowHMinusWeight q p₁ (r + r' - p₂))
      = fun r' => K * Estimates.twoRowHMinusWeight q p₁ (r' + (r - p₂)) := by
    funext r'
    congr 2
    ring
  rw [hfun, torusIntegral_real_const_mul, twoRowWeightAverage]
  congr 1
  exact torusIntegral_comp_add_right (twoRowHMinusWeight_periodic q p₁) (r - p₂)

theorem degreeOneCoefficient_re (q : Estimates.Parameters) (p₁ r : ℝ) :
    (Estimates.degreeOneCoefficient q p₁ r).re = 0 := by
  classical
  rw [Estimates.degreeOneCoefficient]
  by_cases h : r ∈ q.supportInterval |p₁|
  · rw [if_pos h]; simp [Complex.div_re]
  · rw [if_neg h]; simp

theorem degreeOneCoefficient_im_of_mem {q : Estimates.Parameters} {p₁ r : ℝ}
    (h : r ∈ q.supportInterval |p₁|) (hu : Real.sin r ≠ 0) :
    (Estimates.degreeOneCoefficient q p₁ r).im =
      -(Real.sign (Real.sin p₁) / Real.sin r) := by
  classical
  rw [Estimates.degreeOneCoefficient, if_pos h]
  have hu' : ((Real.sin r : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu
  have hrw : -Complex.I * ((Real.sign (Real.sin p₁) : ℝ) : ℂ) / ((Real.sin r : ℝ) : ℂ)
      = ((-(Real.sign (Real.sin p₁) / Real.sin r) : ℝ) : ℂ) * Complex.I := by
    push_cast
    field_simp
  rw [hrw, Complex.mul_I_im, Complex.ofReal_re]

theorem degreeOneCoefficient_of_not_mem {q : Estimates.Parameters} {p₁ r : ℝ}
    (h : r ∉ q.supportInterval |p₁|) :
    Estimates.degreeOneCoefficient q p₁ r = 0 := by
  classical
  rw [Estimates.degreeOneCoefficient, if_neg h]

theorem sin_pos_on_support {q : Estimates.Parameters} {p₁ r : ℝ}
    (hleft : 0 < q.K * q.delta |p₁|) (hright : q.r0 < Real.pi)
    (hr : r ∈ q.supportInterval |p₁|) : 0 < Real.sin r := by
  have h1 : q.K * q.delta |p₁| ≤ r := hr.1
  have h2 : r ≤ q.r0 := hr.2
  exact Real.sin_pos_of_pos_of_lt_pi (lt_of_lt_of_le hleft h1)
    (lt_of_le_of_lt h2 hright)

/-- **The degree-one coefficient has a fixed phase on its support.**  This is
what makes the symmetrized two-row residual dominate each of its halves. -/
theorem degreeOneCoefficient_inner_nonneg {q : Estimates.Parameters} {p₁ : ℝ}
    (hleft : 0 < q.K * q.delta |p₁|) (hright : q.r0 < Real.pi) (r r' : ℝ) :
    0 ≤ (Estimates.degreeOneCoefficient q p₁ r).re *
          (Estimates.degreeOneCoefficient q p₁ r').re +
        (Estimates.degreeOneCoefficient q p₁ r).im *
          (Estimates.degreeOneCoefficient q p₁ r').im := by
  classical
  rw [degreeOneCoefficient_re, zero_mul, zero_add]
  by_cases h1 : r ∈ q.supportInterval |p₁|
  · by_cases h2 : r' ∈ q.supportInterval |p₁|
    · have hs1 := sin_pos_on_support hleft hright h1
      have hs2 := sin_pos_on_support hleft hright h2
      rw [degreeOneCoefficient_im_of_mem h1 hs1.ne',
        degreeOneCoefficient_im_of_mem h2 hs2.ne']
      have heq : -(Real.sign (Real.sin p₁) / Real.sin r) *
          -(Real.sign (Real.sin p₁) / Real.sin r')
          = Real.sign (Real.sin p₁) ^ 2 / (Real.sin r * Real.sin r') := by
        field_simp
      rw [heq]
      positivity
    · rw [degreeOneCoefficient_of_not_mem h2]
      simp
  · rw [degreeOneCoefficient_of_not_mem h1]
    simp

theorem norm_sq_le_norm_add_sq {x y : ℂ} (h : 0 ≤ x.re * y.re + x.im * y.im) :
    ‖x‖ ^ 2 ≤ ‖x + y‖ ^ 2 := by
  have hx : ‖x‖ ^ 2 = x.re ^ 2 + x.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hxy : ‖x + y‖ ^ 2 = (x.re + y.re) ^ 2 + (x.im + y.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im]
    ring
  nlinarith [hx, hxy, sq_nonneg y.re, sq_nonneg y.im]

/-- **Lemma 4.1(d) controls the `α`-average against the degree-one mass.**
The symmetrized two-row residual dominates the half carried by the first row
frequency, and that half integrates to the `α`-average of the weight times the
squared `L²` mass of `f_p`. -/
theorem twoRowWeightAverage_mul_degreeOne_le {q : Estimates.Parameters}
    (hlam : 0 < q.lambda) {p₁ p₂ : ℝ}
    (hleft : 0 < q.K * q.delta |p₁|) (hright : q.r0 < Real.pi)
    (hcert : Estimates.LemmaFourTwoIntegralCertificate q p₁ p₂) :
    twoRowWeightAverage q p₁ * (Real.sin p₁ ^ 2 *
        Estimates.torusIntegral
          (fun r => ‖Estimates.degreeOneCoefficient q p₁ r‖ ^ 2))
      ≤ Estimates.twoRowResidualHMinusSq q p₁ p₂
          (Estimates.degreeOneCoefficient q p₁) := by
  classical
  have hgmeas : Measurable
      (fun r => ‖Estimates.degreeOneCoefficient q p₁ r‖ ^ 2) :=
    (degreeOneCoefficient_measurable q p₁).norm.pow_const 2
  have hgsq : Integrable (fun r => ‖Estimates.degreeOneCoefficient q p₁ r‖ ^ 2)
      (volume.restrict Estimates.torus) := by
    refine (hcert.degreeOneEnergy_integrable.const_mul q.lambda⁻¹).mono'
      hgmeas.aestronglyMeasurable ?_
    filter_upwards with r
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
      Estimates.degreeOneEnergyIntegrand]
    have hd1 := Estimates.dispersion_nonneg p₁
    have hd2 := Estimates.dispersion_nonneg r
    have hinv : (1 : ℝ) ≤ q.lambda⁻¹ *
        (q.lambda + Estimates.dispersion p₁ + Estimates.dispersion r) := by
      rw [← div_eq_inv_mul, le_div_iff₀ hlam]
      linarith
    nlinarith [hinv, sq_nonneg ‖Estimates.degreeOneCoefficient q p₁ r‖]
  have hNnonneg : ∀ z : ℝ × ℝ,
      0 ≤ Estimates.twoRowResidualHMinusIntegrand q p₁ p₂ z := by
    intro z
    rw [Estimates.twoRowResidualHMinusIntegrand]
    exact mul_nonneg (twoRowHMinusWeight_nonneg hlam _ _) (sq_nonneg _)
  have hNmeas : ∀ r : ℝ, Measurable
      (fun r' => Estimates.twoRowResidualHMinusIntegrand q p₁ p₂ (r, r')) := by
    intro r
    exact hcert.twoRowHMinus_measurable.comp (measurable_const.prodMk measurable_id)
  have hNbound : ∀ r r' : ℝ,
      Estimates.twoRowResidualHMinusIntegrand q p₁ p₂ (r, r')
        ≤ q.lambda⁻¹ * (Real.sin p₁ ^ 2 *
            (2 * ‖Estimates.degreeOneCoefficient q p₁ r‖ ^ 2))
          + q.lambda⁻¹ * (Real.sin p₁ ^ 2 * 2) *
            ‖Estimates.degreeOneCoefficient q p₁ r'‖ ^ 2 := by
    intro r r'
    rw [Estimates.twoRowResidualHMinusIntegrand]
    dsimp only
    rw [norm_I_sin_mul_sq]
    have htri := norm_add_le (Estimates.degreeOneCoefficient q p₁ r)
      (Estimates.degreeOneCoefficient q p₁ r')
    have hsq : ‖Estimates.degreeOneCoefficient q p₁ r
          + Estimates.degreeOneCoefficient q p₁ r'‖ ^ 2
        ≤ 2 * ‖Estimates.degreeOneCoefficient q p₁ r‖ ^ 2
          + 2 * ‖Estimates.degreeOneCoefficient q p₁ r'‖ ^ 2 := by
      nlinarith [htri, norm_nonneg (Estimates.degreeOneCoefficient q p₁ r),
        norm_nonneg (Estimates.degreeOneCoefficient q p₁ r'),
        sq_nonneg (‖Estimates.degreeOneCoefficient q p₁ r‖ -
          ‖Estimates.degreeOneCoefficient q p₁ r'‖),
        norm_nonneg (Estimates.degreeOneCoefficient q p₁ r
          + Estimates.degreeOneCoefficient q p₁ r')]
    have hw := twoRowHMinusWeight_le hlam p₁ (r + r' - p₂)
    have hwnn := twoRowHMinusWeight_nonneg hlam p₁ (r + r' - p₂)
    have hsin : (0:ℝ) ≤ Real.sin p₁ ^ 2 := sq_nonneg _
    calc Estimates.twoRowHMinusWeight q p₁ (r + r' - p₂) *
          (Real.sin p₁ ^ 2 * ‖Estimates.degreeOneCoefficient q p₁ r
            + Estimates.degreeOneCoefficient q p₁ r'‖ ^ 2)
        ≤ Estimates.twoRowHMinusWeight q p₁ (r + r' - p₂) *
            (Real.sin p₁ ^ 2 *
              (2 * ‖Estimates.degreeOneCoefficient q p₁ r‖ ^ 2
                + 2 * ‖Estimates.degreeOneCoefficient q p₁ r'‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq hsin) hwnn
      _ ≤ q.lambda⁻¹ *
            (Real.sin p₁ ^ 2 *
              (2 * ‖Estimates.degreeOneCoefficient q p₁ r‖ ^ 2
                + 2 * ‖Estimates.degreeOneCoefficient q p₁ r'‖ ^ 2)) :=
          mul_le_mul_of_nonneg_right hw (by positivity)
      _ = q.lambda⁻¹ * (Real.sin p₁ ^ 2 *
            (2 * ‖Estimates.degreeOneCoefficient q p₁ r‖ ^ 2))
          + q.lambda⁻¹ * (Real.sin p₁ ^ 2 * 2) *
            ‖Estimates.degreeOneCoefficient q p₁ r'‖ ^ 2 := by ring
  have hslice : ∀ r : ℝ, Integrable
      (fun r' => Estimates.twoRowResidualHMinusIntegrand q p₁ p₂ (r, r'))
      (volume.restrict Estimates.torus) := by
    intro r
    have hdom : Integrable
        (fun r' => q.lambda⁻¹ * (Real.sin p₁ ^ 2 *
            (2 * ‖Estimates.degreeOneCoefficient q p₁ r‖ ^ 2))
          + q.lambda⁻¹ * (Real.sin p₁ ^ 2 * 2) *
            ‖Estimates.degreeOneCoefficient q p₁ r'‖ ^ 2)
        (volume.restrict Estimates.torus) :=
      (integrable_const _).add (hgsq.const_mul _)
    refine hdom.mono' (hNmeas r).aestronglyMeasurable ?_
    filter_upwards with r'
    rw [Real.norm_eq_abs, abs_of_nonneg (hNnonneg (r, r'))]
    exact hNbound r r'
  have hinner : ∀ r : ℝ,
      twoRowWeightAverage q p₁ * Real.sin p₁ ^ 2 *
          ‖Estimates.degreeOneCoefficient q p₁ r‖ ^ 2
        ≤ Estimates.torusIntegral
            (fun r' => Estimates.twoRowResidualHMinusIntegrand q p₁ p₂ (r, r')) := by
    intro r
    have hKnn : (0:ℝ) ≤ Real.sin p₁ ^ 2 *
        ‖Estimates.degreeOneCoefficient q p₁ r‖ ^ 2 := by positivity
    have hminorInt : Integrable
        (fun r' => Real.sin p₁ ^ 2 * ‖Estimates.degreeOneCoefficient q p₁ r‖ ^ 2 *
          Estimates.twoRowHMinusWeight q p₁ (r + r' - p₂))
        (volume.restrict Estimates.torus) := by
      refine integrable_torus_of_bound (C := Real.sin p₁ ^ 2 *
        ‖Estimates.degreeOneCoefficient q p₁ r‖ ^ 2 * q.lambda⁻¹) ?_ ?_
      · refine (Measurable.const_mul ?_ _).aestronglyMeasurable
        exact (measurable_twoRowHMinusWeight q p₁).comp (by fun_prop)
      · intro r'
        rw [Real.norm_eq_abs, abs_of_nonneg
          (mul_nonneg hKnn (twoRowHMinusWeight_nonneg hlam _ _))]
        exact mul_le_mul_of_nonneg_left (twoRowHMinusWeight_le hlam _ _) hKnn
    have hptw : ∀ r' : ℝ,
        Real.sin p₁ ^ 2 * ‖Estimates.degreeOneCoefficient q p₁ r‖ ^ 2 *
            Estimates.twoRowHMinusWeight q p₁ (r + r' - p₂)
          ≤ Estimates.twoRowResidualHMinusIntegrand q p₁ p₂ (r, r') := by
      intro r'
      rw [Estimates.twoRowResidualHMinusIntegrand]
      dsimp only
      rw [norm_I_sin_mul_sq]
      have hkey := norm_sq_le_norm_add_sq
        (degreeOneCoefficient_inner_nonneg hleft hright r r')
      have hwnn := twoRowHMinusWeight_nonneg hlam p₁ (r + r' - p₂)
      have hsin : (0:ℝ) ≤ Real.sin p₁ ^ 2 := sq_nonneg _
      calc Real.sin p₁ ^ 2 * ‖Estimates.degreeOneCoefficient q p₁ r‖ ^ 2 *
            Estimates.twoRowHMinusWeight q p₁ (r + r' - p₂)
          = Estimates.twoRowHMinusWeight q p₁ (r + r' - p₂) *
              (Real.sin p₁ ^ 2 * ‖Estimates.degreeOneCoefficient q p₁ r‖ ^ 2) := by ring
        _ ≤ Estimates.twoRowHMinusWeight q p₁ (r + r' - p₂) *
              (Real.sin p₁ ^ 2 * ‖Estimates.degreeOneCoefficient q p₁ r
                + Estimates.degreeOneCoefficient q p₁ r'‖ ^ 2) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hkey hsin) hwnn
    have hmono := torusIntegral_mono hminorInt (hslice r) hptw
    rw [torusIntegral_weight_shift q p₁ p₂ r
      (Real.sin p₁ ^ 2 * ‖Estimates.degreeOneCoefficient q p₁ r‖ ^ 2)] at hmono
    have heq : Real.sin p₁ ^ 2 * ‖Estimates.degreeOneCoefficient q p₁ r‖ ^ 2 *
        twoRowWeightAverage q p₁
        = twoRowWeightAverage q p₁ * Real.sin p₁ ^ 2 *
          ‖Estimates.degreeOneCoefficient q p₁ r‖ ^ 2 := by ring
    rw [heq] at hmono
    exact hmono
  have houterMinor : Integrable
      (fun r => twoRowWeightAverage q p₁ * Real.sin p₁ ^ 2 *
        ‖Estimates.degreeOneCoefficient q p₁ r‖ ^ 2)
      (volume.restrict Estimates.torus) := hgsq.const_mul _
  have houterMajor : Integrable
      (fun r => Estimates.torusIntegral
        (fun r' => Estimates.twoRowResidualHMinusIntegrand q p₁ p₂ (r, r')))
      (volume.restrict Estimates.torus) := by
    have h := Integrable.integral_prod_left hcert.twoRowHMinus_integrable
    have hfun : (fun r => Estimates.torusIntegral
          (fun r' => Estimates.twoRowResidualHMinusIntegrand q p₁ p₂ (r, r')))
        = fun r => (2 * Real.pi)⁻¹ *
          ∫ r' in Estimates.torus, Estimates.twoRowResidualHMinusIntegrand q p₁ p₂ (r, r') := by
      funext r
      rw [Estimates.torusIntegral, smul_eq_mul]
    rw [hfun]
    exact h.const_mul _
  have hfinal := torusIntegral_mono houterMinor houterMajor hinner
  rw [torusIntegral_real_const_mul] at hfinal
  have hgoal : Estimates.twoRowResidualHMinusSq q p₁ p₂
      (Estimates.degreeOneCoefficient q p₁)
      = Estimates.torusIntegral (fun r => Estimates.torusIntegral
        (fun r' => Estimates.twoRowResidualHMinusIntegrand q p₁ p₂ (r, r'))) := rfl
  rw [hgoal]
  calc twoRowWeightAverage q p₁ * (Real.sin p₁ ^ 2 *
        Estimates.torusIntegral
          (fun r => ‖Estimates.degreeOneCoefficient q p₁ r‖ ^ 2))
      = twoRowWeightAverage q p₁ * Real.sin p₁ ^ 2 *
        Estimates.torusIntegral
          (fun r => ‖Estimates.degreeOneCoefficient q p₁ r‖ ^ 2) := by ring
    _ ≤ _ := hfinal

/-! ## Assembly: the two-row half of `summandThreeBound_of_sector_bounds` -/

theorem norm_sq_realTorusL2 (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc (-Real.pi) Real.pi))) :
    ‖Manhattan.realTorusL2 f hf‖ ^ 2 = Estimates.torusIntegral (fun r => ‖f r‖ ^ 2) := by
  have hpi : (-Real.pi) ≤ Real.pi := by linarith [Real.pi_pos]
  have hend : -Real.pi + Manhattan.torusPeriod = Real.pi := by
    rw [Manhattan.torusPeriod]; ring
  have h1 : ‖Manhattan.realTorusL2 f hf‖ ^ 2
      = ∫ x : AddCircle Manhattan.torusPeriod,
          ‖(Manhattan.realTorusL2 f hf : AddCircle Manhattan.torusPeriod → ℂ) x‖ ^ 2
          ∂AddCircle.haarAddCircle := (integral_norm_sq_lp _).symm
  have h2 : (∫ x : AddCircle Manhattan.torusPeriod,
        ‖(Manhattan.realTorusL2 f hf : AddCircle Manhattan.torusPeriod → ℂ) x‖ ^ 2
        ∂AddCircle.haarAddCircle)
      = ∫ x : AddCircle Manhattan.torusPeriod,
          ‖AddCircle.liftIoc Manhattan.torusPeriod (-Real.pi) f x‖ ^ 2
          ∂AddCircle.haarAddCircle := by
    refine integral_congr_ae ?_
    filter_upwards [Manhattan.coeFn_realTorusL2 f hf] with x hx
    rw [hx]
  have h3 : (fun x : AddCircle Manhattan.torusPeriod =>
        ‖AddCircle.liftIoc Manhattan.torusPeriod (-Real.pi) f x‖ ^ 2)
      = fun x => AddCircle.liftIoc Manhattan.torusPeriod (-Real.pi)
          (fun y => ‖f y‖ ^ 2) x := rfl
  rw [h1, h2, h3, AddCircle.integral_haarAddCircle,
    AddCircle.integral_liftIoc_eq_intervalIntegral, hend,
    intervalIntegral.integral_of_le hpi, Estimates.torusIntegral, Estimates.torus,
    Manhattan.torusPeriod]

theorem correctedCompetitor_r0_lt_pi {q : Estimates.Parameters}
    (hK : q.K = correctedCompetitorK) (hrho : q.rho = correctedCompetitorRho) :
    q.r0 < Real.pi := by
  rw [Estimates.Parameters.r0, hK, hrho, correctedCompetitorK, correctedCompetitorRho]
  have hpi := Real.pi_pos
  rw [div_lt_iff₀ (by norm_num)]
  nlinarith

theorem correctedCompetitor_left_pos {q : Estimates.Parameters}
    (hK : q.K = correctedCompetitorK) (hlam : 0 < q.lambda) (a : ℝ) (ha : 0 ≤ a) :
    0 < q.K * q.delta a := by
  rw [hK, correctedCompetitorK, Estimates.Parameters.delta]
  have : 0 < Real.sqrt q.lambda := Real.sqrt_pos.2 hlam
  nlinarith

/-- The uniform constant of Lemma 4.1(d) for the corrected competitor. -/
theorem exists_twoRowResidual_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ q : Estimates.Parameters, q.K = correctedCompetitorK →
      q.rho = correctedCompetitorRho → 0 < q.lambda → q.lambda ≤ 1 →
      ∀ p₁ p₂ : ℝ, p₁ ∈ Estimates.torus → p₂ ∈ Estimates.torus →
        |p₂| ≤ |p₁| → 0 < |p₁| → q.logThreshold < q.scaleLog |p₁| →
        Estimates.twoRowResidualHMinusSq q p₁ p₂
          (Estimates.degreeOneCoefficient q p₁) ≤ C := by
  obtain ⟨cc, C, -, hCpos, hall⟩ :=
    Estimates.lemmaFourTwoSuccessorClaim_proved correctedCompetitorK
      correctedCompetitorRho (by rw [correctedCompetitorK])
      (by rw [correctedCompetitorRho]; positivity)
      (by rw [correctedCompetitorRho])
  refine ⟨C, hCpos, ?_⟩
  intro q hK hrho hlam hlam1 p₁ p₂ hp₁ hp₂ horder hpos hlog
  have hq : (⟨q.lambda, correctedCompetitorK, correctedCompetitorRho⟩ :
      Estimates.Parameters) = q := by
    rw [← hK, ← hrho]
  have h := hall q.lambda hlam hlam1 p₁ p₂ hp₁ hp₂ horder hpos (by rw [hq]; exact hlog)
  rw [hq] at h
  exact h.2.2.2.2.2.2

/-- The two-row sector constant of summand 3. -/
noncomputable def twoRowSummandConstant : ℝ :=
  4 * Classical.choose exists_twoRowResidual_bound

/-- **The two-row `(h,h)` sector bound of summand 3**, in the shape consumed
by `Manhattan.Glue.summandThreeBound_of_sector_bounds`. -/
theorem summandThreeTwoRowSectorBound :
    ∀ q : Estimates.Parameters, q.K = correctedCompetitorK →
        q.rho = correctedCompetitorRho → q.lambda ≤ 1 →
      ∀ (hlambda : 0 < q.lambda) (p : Fin 2 → ℝ), p 0 ∈ Estimates.torus →
        p 1 ∈ Estimates.torus → |p 1| ≤ |p 0| → 0 < |p 0| →
        q.logThreshold < q.scaleLog |p 0| →
      ∀ (hcert : Estimates.LemmaFourTwoIntegralCertificate q (p 0) (p 1))
        (hnormalization : Estimates.degreeOneNormalization q (p 0) ≠ 0),
        (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hlambda
            (Manhattan.type11WalshSynthesis (Manhattan.type11WalshAnalysis
              (walshRaise p (correctedRowVector
                (correctedLowDegreeData hlambda p hcert hnormalization))))) ≤
          twoRowSummandConstant * Real.sqrt (q.scaleLog |p 0|) := by
  intro q hK hrho hlam1 hlambda p hp₀ hp₁ horder hpos hlog hcert hnormalization
  obtain ⟨hCpos, hCall⟩ := Classical.choose_spec exists_twoRowResidual_bound
  set C : ℝ := Classical.choose exists_twoRowResidual_bound with hC
  set c : Manhattan.RowLineCoefficient :=
    fourierBasis.repr (correctedLowDegreeData hlambda p hcert hnormalization).rowFrequency
    with hc
  have hvec : Manhattan.type11WalshAnalysis
      (walshRaise p (correctedRowVector
        (correctedLowDegreeData hlambda p hcert hnormalization)))
      = twoRowRaiseCoeff p c := by
    rw [correctedRowVector_eq_axisDegreeOneSynthesis]
    rfl
  rw [hvec]
  have hmem : MemLp (Estimates.degreeOneCoefficient q (p 0)) 2
      (volume.restrict (Ioc (-Real.pi) Real.pi)) := by
    simpa only [Estimates.torus] using
      degreeOneCoefficient_memLp_of_integralCertificate hlambda hcert
  have hcnorm : ‖c‖ ^ 2
      = Estimates.torusIntegral
        (fun r => ‖Estimates.degreeOneCoefficient q (p 0) r‖ ^ 2) := by
    rw [hc, LinearIsometryEquiv.norm_map, correctedLowDegreeData_row_eq,
      LinearIsometry.norm_map]
    exact norm_sq_realTorusL2 _ hmem
  have hleft := correctedCompetitor_left_pos hK hlambda |p 0| (abs_nonneg _)
  have hright := correctedCompetitor_r0_lt_pi hK hrho
  have hlow := twoRowWeightAverage_mul_degreeOne_le hlambda hleft hright hcert
  have hup := hCall q hK hrho hlambda hlam1 (p 0) (p 1) hp₀ hp₁ horder hpos hlog
  have hstep := hMinusEnergy_twoRowRaiseCoeff_le (q := q) hlambda p c
  have hkey : 4 * twoRowWeightAverage q (p 0) *
      (Real.sin (p 0) ^ 2 * ‖c‖ ^ 2) ≤ 4 * C := by
    rw [hcnorm]
    nlinarith [hlow, hup]
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (q.scaleLog |p 0|) := by
    have h1 := one_le_scaleLog q |p 0|
    have := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_one] at this
  have hCnn : (0 : ℝ) ≤ 4 * C := by linarith
  calc (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hlambda
        (Manhattan.type11WalshSynthesis (twoRowRaiseCoeff p c))
      ≤ 4 * twoRowWeightAverage q (p 0) * (Real.sin (p 0) ^ 2 * ‖c‖ ^ 2) := hstep
    _ ≤ 4 * C := hkey
    _ = twoRowSummandConstant * 1 := by rw [twoRowSummandConstant, ← hC]; ring
    _ ≤ twoRowSummandConstant * Real.sqrt (q.scaleLog |p 0|) := by
        rw [twoRowSummandConstant, ← hC]
        exact mul_le_mul_of_nonneg_left hsqrt hCnn

end

end Manhattan.Glue
