import Manhattan.Estimates.LineResolvent
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Corrected successor to Lemma 4.1

Erratum E-006 shows that the frozen version-one candidate is false at zero
frequency. This file leaves that candidate untouched and proves the exact
successor used by the paper: the sole new hypothesis is `0 < |p₁|`.

Paper: `manuscript.tex:907-958`, with the application-side positivity
hypothesis at `manuscript.tex:1137`.
-/

open MeasureTheory Set

namespace Manhattan.Estimates

noncomputable section

local instance lemmaFourTwoSuccessorPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- Lemma 4.1(a)--(d), corrected only by the hypothesis `0 < |p₁|` found at
its application in `manuscript.tex:1137`. Both `H⁻¹` quantities remain the
explicit weighted integrals defined in `DegreeOne.lean`. -/
def LemmaFourTwoSuccessorClaim (K rho : ℝ) : Prop :=
  20 ≤ K → 0 < rho → rho ≤ Real.pi / 20 →
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ lambda : ℝ, 0 < lambda → lambda ≤ 1 →
    ∀ p₁ p₂ : ℝ, p₁ ∈ torus → p₂ ∈ torus → |p₂| ≤ |p₁| → 0 < |p₁| →
      let q : Parameters := ⟨lambda, K, rho⟩
      q.logThreshold < q.scaleLog |p₁| →
      degreeZeroAdjoint p₁ (degreeOneCoefficient q p₁) =
          -(degreeOneNormalization q p₁ : ℂ) ∧
      c * |p₁| * q.scaleLog |p₁| ≤ degreeOneNormalization q p₁ ∧
      degreeOneEnergy q p₁ ≤ C ∧
      (∀ r : ℝ, mixedResidual q p₁ r = signedSupportIndicator q p₁ r) ∧
      c * q.scaleLog |p₁| ≤ mixedResidualHMinusSq q p₁ ∧
      mixedResidualHMinusSq q p₁ ≤ C * q.scaleLog |p₁| ∧
      twoRowResidualHMinusSq q p₁ p₂ (degreeOneCoefficient q p₁) ≤ C

private theorem successor_r0_pos {q : Parameters} (hq : q.Admissible) : 0 < q.r0 := by
  rw [Parameters.r0]
  exact div_pos hq.2.2.2.1 (mul_pos (by norm_num) (by linarith [hq.2.2.1]))

private theorem successor_r0_le_pi_div_two {q : Parameters} (hq : q.Admissible) :
    q.r0 ≤ Real.pi / 2 := by
  have hr0Rho : q.r0 ≤ q.rho := by
    rw [Parameters.r0]
    exact div_le_self hq.2.2.2.1.le (by nlinarith [hq.2.2.1])
  exact hr0Rho.trans (hq.2.2.2.2.trans (by nlinarith [Real.pi_pos]))

private theorem successor_delta_pos {q : Parameters} (hq : q.Admissible)
    {a : ℝ} (ha : 0 ≤ a) : 0 < q.delta a := by
  rw [Parameters.delta]
  exact add_pos_of_pos_of_nonneg (Real.sqrt_pos.2 hq.1) ha

private theorem torusIntegral_indicator_real (f : ℝ → ℝ) {s : Set ℝ}
    (hs : MeasurableSet s) (hst : s ⊆ torus) :
    torusIntegral (fun x : ℝ => if x ∈ s then f x else 0) =
      (2 * Real.pi)⁻¹ * ∫ x in s, f x := by
  rw [torusIntegral]
  simp only [smul_eq_mul]
  change (2 * Real.pi)⁻¹ * (∫ x in torus, s.indicator f x) = _
  rw [integral_indicator hs, Measure.restrict_restrict hs, inter_eq_left.mpr hst]

private theorem oneCoin_regime {q : Parameters} (hq : q.Admissible) {a : ℝ}
    (ha : 0 ≤ a) (hlog : q.logThreshold < q.scaleLog a) :
    q.K * q.delta a < q.r0 ∧
      q.scaleLog a = 1 + Real.log (q.r0 / q.delta a) ∧
      q.scaleLog a / 2 ≤ Real.log (q.r0 / (q.K * q.delta a)) := by
  have hKPos : 0 < q.K := by linarith [hq.2.2.1]
  have hKOne : 1 < q.K := by linarith [hq.2.2.1]
  have hlogKPos : 0 < Real.log q.K := Real.log_pos hKOne
  have hdeltaPos : 0 < q.delta a := successor_delta_pos hq ha
  have hr0Pos : 0 < q.r0 := successor_r0_pos hq
  have hlogPosPositive : 0 < logPos (q.r0 / q.delta a) := by
    dsimp [Parameters.logThreshold, Parameters.scaleLog] at hlog
    nlinarith
  have hrawPositive : 0 < Real.log (q.r0 / q.delta a) := by
    by_contra h
    have hnonpos : Real.log (q.r0 / q.delta a) ≤ 0 := le_of_not_gt h
    rw [logPos, max_eq_left hnonpos] at hlogPosPositive
    exact lt_irrefl 0 hlogPosPositive
  have hscale : q.scaleLog a = 1 + Real.log (q.r0 / q.delta a) := by
    rw [Parameters.scaleLog, logPos, max_eq_right hrawPositive.le]
  have hlogKRatio : Real.log q.K < Real.log (q.r0 / q.delta a) := by
    rw [hscale] at hlog
    dsimp [Parameters.logThreshold] at hlog
    nlinarith
  have hratioPos : 0 < q.r0 / q.delta a := div_pos hr0Pos hdeltaPos
  have hKRatio : q.K < q.r0 / q.delta a :=
    (Real.log_lt_log_iff hKPos hratioPos).mp hlogKRatio
  have hsupport : q.K * q.delta a < q.r0 := (lt_div_iff₀ hdeltaPos).mp hKRatio
  have hlogInterval : q.scaleLog a / 2 ≤ Real.log (q.r0 / (q.K * q.delta a)) := by
    have hidentity : Real.log (q.r0 / (q.K * q.delta a)) =
        Real.log (q.r0 / q.delta a) - Real.log q.K := by
      rw [Real.log_div hr0Pos.ne' (mul_pos hKPos hdeltaPos).ne',
        Real.log_div hr0Pos.ne' hdeltaPos.ne', Real.log_mul hKPos.ne' hdeltaPos.ne']
      ring
    rw [hidentity, hscale] at ⊢
    rw [hscale] at hlog
    dsimp [Parameters.logThreshold] at hlog
    nlinarith
  exact ⟨hsupport, hscale, hlogInterval⟩

private theorem degreeOneNormalization_integral_lower {q : Parameters} (hq : q.Admissible)
    {a : ℝ} (ha : 0 ≤ a) (hsupport : q.K * q.delta a < q.r0) :
    (2 * Real.pi)⁻¹ * Real.log (q.r0 / (q.K * q.delta a)) ≤
      torusIntegral (fun r : ℝ =>
        if r ∈ q.supportInterval a then (Real.sin r)⁻¹ else 0) := by
  have hleftPos : 0 < q.K * q.delta a :=
    mul_pos (by linarith [hq.2.2.1]) (successor_delta_pos hq ha)
  have hr0Pos : 0 < q.r0 := successor_r0_pos hq
  have hsubset : q.supportInterval a ⊆ torus := by
    intro r hr
    exact ⟨(neg_lt_zero.mpr Real.pi_pos).trans (hleftPos.trans_le hr.1),
      hr.2.trans (successor_r0_le_pi_div_two hq) |>.trans (by linarith [Real.pi_pos])⟩
  have hinvCont : ContinuousOn (fun r : ℝ => (Real.sin r)⁻¹) (q.supportInterval a) := by
    apply ContinuousOn.inv₀ Real.continuous_sin.continuousOn
    intro r hr
    have hrPos : 0 < r := hleftPos.trans_le hr.1
    have hrPi : r < Real.pi :=
      (hr.2.trans (successor_r0_le_pi_div_two hq)).trans_lt (by linarith [Real.pi_pos])
    exact (Real.sin_pos_of_mem_Ioo ⟨hrPos, hrPi⟩).ne'
  have honeCont : ContinuousOn (fun r : ℝ => r⁻¹) (q.supportInterval a) := by
    apply ContinuousOn.inv₀ continuous_id.continuousOn
    intro r hr
    exact (hleftPos.trans_le hr.1).ne'
  have hpoint : ∀ r ∈ q.supportInterval a, r⁻¹ ≤ (Real.sin r)⁻¹ := by
    intro r hr
    have hrPos : 0 < r := hleftPos.trans_le hr.1
    have hsinPos : 0 < Real.sin r := by
      apply Real.sin_pos_of_mem_Ioo
      exact ⟨hrPos, (hr.2.trans (successor_r0_le_pi_div_two hq)).trans_lt
        (by linarith [Real.pi_pos])⟩
    exact (inv_le_inv₀ hrPos hsinPos).2 (Real.sin_le hrPos.le)
  have hmono : (∫ r in q.supportInterval a, r⁻¹) ≤
      ∫ r in q.supportInterval a, (Real.sin r)⁻¹ :=
    setIntegral_mono_on honeCont.integrableOn_Icc hinvCont.integrableOn_Icc
      measurableSet_Icc hpoint
  have htorusEq := torusIntegral_indicator_real (s := q.supportInterval a)
    (fun r : ℝ => (Real.sin r)⁻¹) measurableSet_Icc hsubset
  rw [htorusEq]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    Real.log (q.r0 / (q.K * q.delta a)) =
        ∫ r in q.K * q.delta a..q.r0, r⁻¹ :=
          (integral_inv_of_pos hleftPos hr0Pos).symm
    _ = ∫ r in q.supportInterval a, r⁻¹ := by
      rw [Parameters.supportInterval, integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le hsupport.le]
    _ ≤ _ := hmono

private theorem degreeZeroAdjoint_degreeOneCoefficient {q : Parameters} {p₁ : ℝ} :
    degreeZeroAdjoint p₁ (degreeOneCoefficient q p₁) =
      -(degreeOneNormalization q p₁ : ℂ) := by
  let base : ℝ → ℝ := fun r =>
    if r ∈ q.supportInterval |p₁| then (Real.sin r)⁻¹ else 0
  let z : ℂ := -Complex.I * (Real.sign (Real.sin p₁) : ℂ)
  have hcoeff : ∀ r : ℝ, degreeOneCoefficient q p₁ r = z * (base r : ℂ) := by
    intro r
    by_cases hr : r ∈ q.supportInterval |p₁|
    · simp only [degreeOneCoefficient, base, z, hr, if_pos]
      rw [Complex.ofReal_inv]
      ring
    · simp [degreeOneCoefficient, base, hr]
  have hintegral : torusIntegral (degreeOneCoefficient q p₁) =
      z * ((torusIntegral base : ℝ) : ℂ) := by
    rw [torusIntegral, torusIntegral]
    simp_rw [hcoeff]
    rw [integral_const_mul, integral_complex_ofReal]
    simp only [Complex.real_smul, smul_eq_mul]
    push_cast
    ring
  rw [degreeZeroAdjoint, degreeOneNormalization, hintegral]
  dsimp [z, base]
  have hsign : Real.sin p₁ * Real.sign (Real.sin p₁) = |Real.sin p₁| := by
    rcases lt_trichotomy (Real.sin p₁) 0 with hneg | hzero | hpos
    · rw [Real.sign_of_neg hneg, abs_of_neg hneg]
      ring
    · rw [hzero, Real.sign_zero, abs_zero]
      ring
    · rw [Real.sign_of_pos hpos, abs_of_pos hpos]
      ring
  have hsignC : (Real.sin p₁ : ℂ) * (Real.sign (Real.sin p₁) : ℂ) =
      ((|Real.sin p₁| : ℝ) : ℂ) := by exact_mod_cast hsign
  rw [Complex.ofReal_mul]
  change -Complex.I * (Real.sin p₁ : ℂ) *
      (-Complex.I * (Real.sign (Real.sin p₁) : ℂ) *
        ((torusIntegral base : ℝ) : ℂ)) =
      -(((|Real.sin p₁| : ℝ) : ℂ) * ((torusIntegral base : ℝ) : ℂ))
  rw [← hsignC]
  ring_nf
  simp [Complex.I_sq]

private theorem degreeOneNormalization_lower {q : Parameters} (hq : q.Admissible)
    {p₁ : ℝ} (hpPos : 0 < |p₁|)
    (hsupport : q.K * q.delta |p₁| < q.r0)
    (hlogInterval : q.scaleLog |p₁| / 2 ≤
      Real.log (q.r0 / (q.K * q.delta |p₁|))) :
    (1 / (4000 * Real.pi)) * |p₁| * q.scaleLog |p₁| ≤
      degreeOneNormalization q p₁ := by
  let I : ℝ := torusIntegral (fun r : ℝ =>
    if r ∈ q.supportInterval |p₁| then (Real.sin r)⁻¹ else 0)
  have hdeltaPos := successor_delta_pos hq (abs_nonneg p₁)
  have hpDelta : |p₁| ≤ q.delta |p₁| := by
    rw [Parameters.delta]
    exact le_add_of_nonneg_left (Real.sqrt_nonneg _)
  have hpR0 : |p₁| < q.r0 := by
    have hKOne : 1 ≤ q.K := by linarith [hq.2.2.1]
    calc
      |p₁| ≤ q.delta |p₁| := hpDelta
      _ ≤ q.K * q.delta |p₁| := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hKOne hdeltaPos.le
      _ < q.r0 := hsupport
  have hpSmall : |p₁| ≤ Real.pi / 2 := hpR0.le.trans (successor_r0_le_pi_div_two hq)
  have hjordan := Real.mul_abs_le_abs_sin hpSmall
  have hsinLower : |p₁| / 2 ≤ |Real.sin p₁| := by
    calc
      |p₁| / 2 ≤ (2 / Real.pi) * |p₁| := by
        have hc : (1 / 2 : ℝ) ≤ 2 / Real.pi := by
          rw [le_div_iff₀ Real.pi_pos]
          nlinarith [Real.pi_le_four]
        simpa only [div_eq_mul_inv, one_mul, mul_comm] using
          mul_le_mul_of_nonneg_right hc (abs_nonneg p₁)
      _ ≤ |Real.sin p₁| := hjordan
  have hIlog := degreeOneNormalization_integral_lower hq (abs_nonneg p₁) hsupport
  have hIL : (1 / (4 * Real.pi)) * q.scaleLog |p₁| ≤ I := by
    dsimp [I]
    calc
      (1 / (4 * Real.pi)) * q.scaleLog |p₁| =
          (2 * Real.pi)⁻¹ * (q.scaleLog |p₁| / 2) := by
            field_simp [Real.pi_ne_zero]
            ring
      _ ≤ (2 * Real.pi)⁻¹ * Real.log (q.r0 / (q.K * q.delta |p₁|)) := by
        gcongr
      _ ≤ _ := hIlog
  have hLPos : 0 < q.scaleLog |p₁| := by
    rw [Parameters.scaleLog]
    exact add_pos_of_pos_of_nonneg zero_lt_one (le_max_left _ _)
  have hIPos : 0 < I := (mul_pos (by positivity) hLPos).trans_le hIL
  have hproduct : (|p₁| / 2) * ((1 / (4 * Real.pi)) * q.scaleLog |p₁|) ≤
      |Real.sin p₁| * I :=
    mul_le_mul hsinLower hIL (mul_nonneg (by positivity) hLPos.le) (abs_nonneg _)
  rw [degreeOneNormalization]
  change (1 / (4000 * Real.pi)) * |p₁| * q.scaleLog |p₁| ≤
    |Real.sin p₁| * I
  calc
    (1 / (4000 * Real.pi)) * |p₁| * q.scaleLog |p₁| ≤
        (|p₁| / 2) * ((1 / (4 * Real.pi)) * q.scaleLog |p₁|) := by
          have hpNonneg := hpPos.le
          field_simp [Real.pi_ne_zero]
          nlinarith [Real.pi_pos, mul_nonneg hpNonneg hLPos.le]
    _ ≤ _ := hproduct

private theorem successor_torusIntegral_const_mul (c : ℝ) (f : ℝ → ℝ) :
    torusIntegral (fun x => c * f x) = c * torusIntegral f := by
  simp only [torusIntegral, integral_const_mul, smul_eq_mul]
  ring

private theorem degreeOneEnergy_le {q : Parameters} (hq : q.Admissible)
    {p₁ : ℝ} (hpPos : 0 < |p₁|)
    (hsupport : q.K * q.delta |p₁| < q.r0) : degreeOneEnergy q p₁ ≤ 4 := by
  let e : ℝ → ℝ := fun r =>
    (q.lambda + dispersion p₁ + dispersion r) * ‖degreeOneCoefficient q p₁ r‖ ^ 2
  have hdeltaPos := successor_delta_pos hq (abs_nonneg p₁)
  have hKPos : 0 < q.K := by linarith [hq.2.2.1]
  have hleftPos : 0 < q.K * q.delta |p₁| := mul_pos hKPos hdeltaPos
  have hpDelta : |p₁| ≤ q.delta |p₁| := by
    rw [Parameters.delta]
    exact le_add_of_nonneg_left (Real.sqrt_nonneg _)
  have hpR0 : |p₁| < q.r0 := by
    have hKOne : 1 ≤ q.K := by linarith [hq.2.2.1]
    exact hpDelta.trans (by
      simpa only [one_mul] using
        (mul_le_mul_of_nonneg_right hKOne hdeltaPos.le)) |>.trans_lt hsupport
  have hpSmall : |p₁| ≤ Real.pi / 2 := hpR0.le.trans (successor_r0_le_pi_div_two hq)
  have hsinpNe : Real.sin p₁ ≠ 0 := by
    have hpAbsPi : |p₁| < Real.pi := hpSmall.trans_lt (by linarith [Real.pi_pos])
    rcases lt_or_gt_of_ne (abs_pos.mp hpPos) with hpNeg | hpRawPos
    · exact (Real.sin_neg_of_neg_of_neg_pi_lt hpNeg (by
        exact (neg_lt_neg hpAbsPi).trans_le (neg_abs_le p₁))).ne
    · exact (Real.sin_pos_of_pos_of_lt_pi hpRawPos
        ((le_abs_self p₁).trans_lt hpAbsPi)).ne'
  have hsignAbs : |Real.sign (Real.sin p₁)| = 1 := by
    rcases Real.sign_apply_eq_of_ne_zero (Real.sin p₁) hsinpNe with hsign | hsign
    · rw [hsign]
      norm_num
    · rw [hsign]
      norm_num
  have hpoint : ∀ r : ℝ, e r ≤ 4 := by
    intro r
    by_cases hr : r ∈ q.supportInterval |p₁|
    · have hrPos : 0 < r := hleftPos.trans_le hr.1
      have hrSmall : r ≤ Real.pi / 2 := hr.2.trans (successor_r0_le_pi_div_two hq)
      have hrAbs : |r| ≤ Real.pi := by
        rw [abs_of_pos hrPos]
        exact hrSmall.trans (by linarith [Real.pi_pos])
      have hpAbs : |p₁| ≤ Real.pi := hpSmall.trans (by linarith [Real.pi_pos])
      have hdp := (dispersion_quadratic_bounds hpAbs).2
      have hdr := (dispersion_quadratic_bounds hrAbs).2
      have hsqrtSq : (Real.sqrt q.lambda) ^ 2 = q.lambda := Real.sq_sqrt hq.1.le
      have hlamDelta : q.lambda ≤ q.delta |p₁| ^ 2 := by
        rw [Parameters.delta]
        nlinarith [Real.sqrt_nonneg q.lambda,
          mul_nonneg (Real.sqrt_nonneg q.lambda) (abs_nonneg p₁)]
      have hpSqDelta : p₁ ^ 2 ≤ q.delta |p₁| ^ 2 := by
        rw [← sq_abs p₁]
        exact sq_le_sq₀ (abs_nonneg p₁) hdeltaPos.le |>.2 hpDelta
      have hdeltaR : q.delta |p₁| ≤ r / q.K := by
        rw [le_div_iff₀ hKPos]
        simpa only [mul_comm] using hr.1
      have hdeltaSq : q.delta |p₁| ^ 2 ≤ r ^ 2 / 400 := by
        have htwenty : 20 ≤ q.K := hq.2.2.1
        have hdeltaTwenty : 20 * q.delta |p₁| ≤ r := by
          calc
            20 * q.delta |p₁| ≤ q.K * q.delta |p₁| := by gcongr
            _ ≤ r := hr.1
        nlinarith [sq_nonneg (r - 20 * q.delta |p₁|)]
      have hnum : q.lambda + dispersion p₁ + dispersion r ≤ r ^ 2 := by
        nlinarith
      have hjordan := Real.mul_abs_le_abs_sin
        (show |r| ≤ Real.pi / 2 by rw [abs_of_pos hrPos]; exact hrSmall)
      have hsinLower : r / 2 ≤ Real.sin r := by
        have hsinPos : 0 < Real.sin r := Real.sin_pos_of_pos_of_lt_pi hrPos
          (hrSmall.trans_lt (by linarith [Real.pi_pos]))
        calc
          r / 2 = |r| / 2 := by rw [abs_of_pos hrPos]
          _ ≤ (2 / Real.pi) * |r| := by
            have hc : (1 / 2 : ℝ) ≤ 2 / Real.pi := by
              rw [le_div_iff₀ Real.pi_pos]
              nlinarith [Real.pi_le_four]
            simpa only [div_eq_mul_inv, one_mul, mul_comm] using
              mul_le_mul_of_nonneg_right hc (abs_nonneg r)
          _ ≤ |Real.sin r| := hjordan
          _ = Real.sin r := abs_of_pos hsinPos
      have hsinSq : r ^ 2 / 4 ≤ Real.sin r ^ 2 := by
        nlinarith [sq_nonneg (Real.sin r - r / 2)]
      have hsinSqPos : 0 < Real.sin r ^ 2 := sq_pos_of_ne_zero
        (Real.sin_pos_of_pos_of_lt_pi hrPos
          (hrSmall.trans_lt (by linarith [Real.pi_pos]))).ne'
      have hquotient : (q.lambda + dispersion p₁ + dispersion r) /
          Real.sin r ^ 2 ≤ 4 := by
        apply (div_le_iff₀ hsinSqPos).2
        nlinarith [dispersion_nonneg p₁, dispersion_nonneg r, hq.1]
      dsimp [e]
      simp only [degreeOneCoefficient, hr, if_pos, norm_div, norm_mul,
        norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        hsignAbs, one_div, one_mul, inv_pow, sq_abs]
      simpa only [div_eq_mul_inv] using hquotient
    · dsimp [e]
      simp [degreeOneCoefficient, hr]
  rw [degreeOneEnergy]
  change torusIntegral e ≤ 4
  have heMeasurable : Measurable e := by
    have hf : Measurable (degreeOneCoefficient q p₁) := by
      unfold degreeOneCoefficient
      apply Measurable.ite measurableSet_Icc
      · fun_prop
      · exact measurable_const
    have hw : Measurable (fun r : ℝ =>
        q.lambda + dispersion p₁ + dispersion r) := by
      unfold dispersion
      fun_prop
    dsimp [e]
    exact hw.mul (hf.norm.pow_const 2)
  have heNonneg : ∀ r : ℝ, 0 ≤ e r := by
    intro r
    dsimp [e]
    exact mul_nonneg
      (add_nonneg (add_nonneg hq.1.le (dispersion_nonneg p₁)) (dispersion_nonneg r))
      (sq_nonneg _)
  letI : IsFiniteMeasure (volume.restrict torus) := ⟨by
    rw [Measure.restrict_apply_univ, torus]
    exact measure_Ioc_lt_top⟩
  have he : Integrable e (volume.restrict torus) := by
    apply Integrable.of_bound heMeasurable.aestronglyMeasurable 4
    filter_upwards with r
    rw [Real.norm_eq_abs, abs_of_nonneg (heNonneg r)]
    exact hpoint r
  have hconstInt : Integrable (fun _ : ℝ => (4 : ℝ)) (volume.restrict torus) :=
    integrable_const 4
  have hmono : torusIntegral e ≤ torusIntegral (fun _ : ℝ => (4 : ℝ)) := by
    rw [torusIntegral, torusIntegral]
    simp only [smul_eq_mul]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact integral_mono he hconstInt hpoint
  calc
    torusIntegral e ≤ torusIntegral (fun _ : ℝ => (4 : ℝ)) := hmono
    _ = 4 * torusIntegral (fun _ : ℝ => (1 : ℝ)) := by
      simpa only [mul_one] using
        successor_torusIntegral_const_mul 4 (fun _ : ℝ => 1)
    _ = 4 := by rw [torusIntegral_one]; norm_num

private noncomputable def mixedRadialKernel (q : Parameters) (r : ℝ) : ℝ :=
  (Real.sqrt ((q.lambda + dispersion r) *
    (q.lambda + dispersion r + 2)))⁻¹

private theorem mixedResidualHMinusSq_eq_radial {q : Parameters}
    (hq : q.Admissible) {p₁ : ℝ} (hsinpNe : Real.sin p₁ ≠ 0)
    (hleft : 0 < q.K * q.delta |p₁|) (hright : q.r0 < Real.pi) :
    mixedResidualHMinusSq q p₁ = torusIntegral (fun r : ℝ =>
      if r ∈ q.supportInterval |p₁| then mixedRadialKernel q r else 0) := by
  have hsignAbs : |Real.sign (Real.sin p₁)| = 1 := by
    rcases Real.sign_apply_eq_of_ne_zero (Real.sin p₁) hsinpNe with hsign | hsign
    · rw [hsign]
      norm_num
    · rw [hsign]
      norm_num
  rw [mixedResidualHMinusSq]
  apply congrArg torusIntegral
  funext r
  have hmu : 0 < q.lambda + dispersion r :=
    add_pos_of_pos_of_nonneg hq.1 (dispersion_nonneg r)
  have hline := lineResolventIdentity_proved (q.lambda + dispersion r) hmu
  have hinner : torusIntegral (fun beta : ℝ =>
      mixedHMinusWeight q r beta * ‖mixedResidual q p₁ r‖ ^ 2) =
      mixedRadialKernel q r * ‖mixedResidual q p₁ r‖ ^ 2 := by
    calc
      torusIntegral (fun beta : ℝ =>
          mixedHMinusWeight q r beta * ‖mixedResidual q p₁ r‖ ^ 2) =
          ‖mixedResidual q p₁ r‖ ^ 2 * torusIntegral (fun beta : ℝ =>
            (q.lambda + dispersion r + dispersion beta)⁻¹) := by
              rw [← successor_torusIntegral_const_mul]
              apply congrArg torusIntegral
              funext beta
              simp only [mixedHMinusWeight]
              ring
      _ = mixedRadialKernel q r * ‖mixedResidual q p₁ r‖ ^ 2 := by
        rw [hline]
        dsimp [mixedRadialKernel]
        ring
  rw [hinner, mixedResidual_eq_indicator hleft hright]
  by_cases hr : r ∈ q.supportInterval |p₁|
  · simp only [signedSupportIndicator, hr, if_pos, Complex.norm_real,
      Real.norm_eq_abs, hsignAbs, one_pow, mul_one]
  · simp [signedSupportIndicator, hr]

private theorem mixedRadialKernel_continuous {q : Parameters} (hq : q.Admissible) :
    Continuous (mixedRadialKernel q) := by
  let mu : ℝ → ℝ := fun r => q.lambda + dispersion r
  have hmuContinuous : Continuous mu := by
    dsimp [mu, dispersion]
    fun_prop
  have hrootContinuous : Continuous (fun r : ℝ =>
      Real.sqrt (mu r * (mu r + 2))) := (hmuContinuous.mul
        (hmuContinuous.add continuous_const)).sqrt
  apply Continuous.inv₀ hrootContinuous
  intro r
  apply (Real.sqrt_pos.2 _).ne'
  exact mul_pos (add_pos_of_pos_of_nonneg hq.1 (dispersion_nonneg r))
    (by linarith [hq.1, dispersion_nonneg r])

private theorem mixedRadialKernel_bounds {q : Parameters} (hq : q.Admissible)
    {a r : ℝ} (ha : 0 ≤ a)
    (hr : r ∈ q.supportInterval a) :
    (4 * r)⁻¹ ≤ mixedRadialKernel q r ∧ mixedRadialKernel q r ≤ 2 * r⁻¹ := by
  have hdeltaPos := successor_delta_pos hq ha
  have hKPos : 0 < q.K := by linarith [hq.2.2.1]
  have hleftPos : 0 < q.K * q.delta a := mul_pos hKPos hdeltaPos
  have hrPos : 0 < r := hleftPos.trans_le hr.1
  have hrSmall : r ≤ Real.pi / 2 := hr.2.trans (successor_r0_le_pi_div_two hq)
  have hrAbs : |r| ≤ Real.pi := by
    rw [abs_of_pos hrPos]
    exact hrSmall.trans (by linarith [Real.pi_pos])
  have hdr := dispersion_quadratic_bounds hrAbs
  have hsqrtSq : (Real.sqrt q.lambda) ^ 2 = q.lambda := Real.sq_sqrt hq.1.le
  have hlamDelta : q.lambda ≤ q.delta a ^ 2 := by
    rw [Parameters.delta]
    nlinarith [Real.sqrt_nonneg q.lambda,
      mul_nonneg (Real.sqrt_nonneg q.lambda) ha]
  have hdeltaSq : q.delta a ^ 2 ≤ r ^ 2 / 400 := by
    have hdeltaTwenty : 20 * q.delta a ≤ r := by
      calc
        20 * q.delta a ≤ q.K * q.delta a :=
          mul_le_mul_of_nonneg_right hq.2.2.1 hdeltaPos.le
        _ ≤ r := hr.1
    nlinarith [sq_nonneg (r - 20 * q.delta a)]
  let mu : ℝ := q.lambda + dispersion r
  have hmuPos : 0 < mu := add_pos_of_pos_of_nonneg hq.1 (dispersion_nonneg r)
  have hmuUpper : mu ≤ r ^ 2 := by
    dsimp [mu]
    nlinarith
  have hmuLower : r ^ 2 / 8 ≤ mu := by
    dsimp [mu]
    have hpiSq : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_pos, Real.pi_le_four]
    have hquad : r ^ 2 / 8 ≤ 2 * r ^ 2 / Real.pi ^ 2 := by
      rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 8)
        (sq_pos_of_pos Real.pi_pos)]
      nlinarith [sq_nonneg r]
    exact hquad.trans (hdr.1.trans (le_add_of_nonneg_left hq.1.le))
  have hrSqLe : r ^ 2 ≤ 4 := by
    nlinarith [Real.pi_pos, Real.pi_le_four, sq_nonneg (r - 2)]
  have hprodPos : 0 < mu * (mu + 2) := mul_pos hmuPos (by linarith)
  have hprodUpper : mu * (mu + 2) ≤ (4 * r) ^ 2 := by
    nlinarith [mul_nonneg hmuPos.le (by linarith : 0 ≤ mu + 2)]
  have hprodLower : (r / 2) ^ 2 ≤ mu * (mu + 2) := by
    nlinarith [mul_nonneg hmuPos.le (by linarith : 0 ≤ mu + 2)]
  have hrootPos : 0 < Real.sqrt (mu * (mu + 2)) := Real.sqrt_pos.2 hprodPos
  have hrootUpper : Real.sqrt (mu * (mu + 2)) ≤ 4 * r := by
    rw [← Real.sqrt_sq (mul_nonneg (by norm_num) hrPos.le)]
    exact Real.sqrt_le_sqrt hprodUpper
  have hrootLower : r / 2 ≤ Real.sqrt (mu * (mu + 2)) := by
    rw [← Real.sqrt_sq (by linarith : 0 ≤ r / 2)]
    exact Real.sqrt_le_sqrt hprodLower
  dsimp [mixedRadialKernel]
  constructor
  · exact (inv_le_inv₀ (mul_pos (by norm_num) hrPos) hrootPos).2 hrootUpper
  · calc
      (Real.sqrt (mu * (mu + 2)))⁻¹ ≤ (r / 2)⁻¹ :=
        (inv_le_inv₀ hrootPos (by linarith : 0 < r / 2)).2 hrootLower
      _ = 2 * r⁻¹ := by field_simp

private theorem mixedResidualHMinusSq_bounds {q : Parameters} (hq : q.Admissible)
    {p₁ : ℝ} (hpPos : 0 < |p₁|)
    (hsupport : q.K * q.delta |p₁| < q.r0)
    (hscale : q.scaleLog |p₁| = 1 + Real.log (q.r0 / q.delta |p₁|))
    (hlogInterval : q.scaleLog |p₁| / 2 ≤
      Real.log (q.r0 / (q.K * q.delta |p₁|))) :
    (1 / (4000 * Real.pi)) * q.scaleLog |p₁| ≤
        mixedResidualHMinusSq q p₁ ∧
      mixedResidualHMinusSq q p₁ ≤ q.scaleLog |p₁| := by
  have hdeltaPos := successor_delta_pos hq (abs_nonneg p₁)
  have hKPos : 0 < q.K := by linarith [hq.2.2.1]
  have hleftPos : 0 < q.K * q.delta |p₁| := mul_pos hKPos hdeltaPos
  have hr0Pos := successor_r0_pos hq
  have hrightPi : q.r0 < Real.pi :=
    (successor_r0_le_pi_div_two hq).trans_lt (by linarith [Real.pi_pos])
  have hpDelta : |p₁| ≤ q.delta |p₁| := by
    rw [Parameters.delta]
    exact le_add_of_nonneg_left (Real.sqrt_nonneg _)
  have hpR0 : |p₁| < q.r0 := by
    have hKOne : 1 ≤ q.K := by linarith [hq.2.2.1]
    exact hpDelta.trans (by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hKOne hdeltaPos.le) |>.trans_lt hsupport
  have hpSmall : |p₁| ≤ Real.pi / 2 := hpR0.le.trans (successor_r0_le_pi_div_two hq)
  have hsinpNe : Real.sin p₁ ≠ 0 := by
    have hpAbsPi : |p₁| < Real.pi := hpSmall.trans_lt (by linarith [Real.pi_pos])
    rcases lt_or_gt_of_ne (abs_pos.mp hpPos) with hpNeg | hpRawPos
    · exact (Real.sin_neg_of_neg_of_neg_pi_lt hpNeg
        ((neg_lt_neg hpAbsPi).trans_le (neg_abs_le p₁))).ne
    · exact (Real.sin_pos_of_pos_of_lt_pi hpRawPos
        ((le_abs_self p₁).trans_lt hpAbsPi)).ne'
  rw [mixedResidualHMinusSq_eq_radial hq hsinpNe hleftPos hrightPi]
  have hsubset : q.supportInterval |p₁| ⊆ torus := by
    intro r hr
    exact ⟨(neg_lt_zero.mpr Real.pi_pos).trans (hleftPos.trans_le hr.1),
      hr.2.trans_lt hrightPi |>.le⟩
  rw [torusIntegral_indicator_real (s := q.supportInterval |p₁|)
    (mixedRadialKernel q) measurableSet_Icc hsubset]
  have hkernelInt : IntegrableOn (mixedRadialKernel q)
      (q.supportInterval |p₁|) := by
    rw [Parameters.supportInterval]
    exact (mixedRadialKernel_continuous hq).continuousOn.integrableOn_Icc
  have hlowerInt : (∫ r in q.supportInterval |p₁|, (4 * r)⁻¹) ≤
      ∫ r in q.supportInterval |p₁|, mixedRadialKernel q r := by
    apply setIntegral_mono_on
    · have hc : ContinuousOn (fun r : ℝ => (4 * r)⁻¹)
          (q.supportInterval |p₁|) := by
        apply ContinuousOn.inv₀ (continuous_const.mul continuous_id).continuousOn
        intro r hr
        exact (mul_pos (by norm_num) (hleftPos.trans_le hr.1)).ne'
      exact hc.integrableOn_Icc
    · exact hkernelInt
    · exact measurableSet_Icc
    · intro r hr
      exact (mixedRadialKernel_bounds hq (abs_nonneg p₁) hr).1
  have hupperInt : (∫ r in q.supportInterval |p₁|, mixedRadialKernel q r) ≤
      ∫ r in q.supportInterval |p₁|, 2 * r⁻¹ := by
    apply setIntegral_mono_on
    · exact hkernelInt
    · have hc : ContinuousOn (fun r : ℝ => 2 * r⁻¹)
          (q.supportInterval |p₁|) := by
        have hinv : ContinuousOn (fun r : ℝ => r⁻¹)
            (q.supportInterval |p₁|) := by
          apply ContinuousOn.inv₀ continuous_id.continuousOn
          intro r hr
          exact (hleftPos.trans_le hr.1).ne'
        exact continuousOn_const.mul hinv
      exact hc.integrableOn_Icc
    · exact measurableSet_Icc
    · intro r hr
      exact (mixedRadialKernel_bounds hq (abs_nonneg p₁) hr).2
  have hinvIntegral : (∫ r in q.supportInterval |p₁|, r⁻¹) =
      Real.log (q.r0 / (q.K * q.delta |p₁|)) := by
    rw [Parameters.supportInterval, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hsupport.le,
      integral_inv_of_pos hleftPos hr0Pos]
  have hlowerExact : (∫ r in q.supportInterval |p₁|, (4 * r)⁻¹) =
      (1 / 4 : ℝ) * Real.log (q.r0 / (q.K * q.delta |p₁|)) := by
    rw [show (fun r : ℝ => (4 * r)⁻¹) = fun r : ℝ => (1 / 4 : ℝ) * r⁻¹ by
      funext r
      ring, integral_const_mul, hinvIntegral]
  have hupperExact : (∫ r in q.supportInterval |p₁|, 2 * r⁻¹) =
      2 * Real.log (q.r0 / (q.K * q.delta |p₁|)) := by
    rw [integral_const_mul, hinvIntegral]
  have hlogUpper : Real.log (q.r0 / (q.K * q.delta |p₁|)) ≤
      q.scaleLog |p₁| := by
    have hlogKNonneg : 0 ≤ Real.log q.K := Real.log_nonneg (by linarith [hq.2.2.1])
    have hidentity : Real.log (q.r0 / (q.K * q.delta |p₁|)) =
        Real.log (q.r0 / q.delta |p₁|) - Real.log q.K := by
      rw [Real.log_div hr0Pos.ne' (mul_pos hKPos hdeltaPos).ne',
        Real.log_div hr0Pos.ne' hdeltaPos.ne', Real.log_mul hKPos.ne' hdeltaPos.ne']
      ring
    rw [hidentity, hscale]
    linarith
  have hLPos : 0 < q.scaleLog |p₁| := by
    rw [Parameters.scaleLog]
    exact add_pos_of_pos_of_nonneg zero_lt_one (le_max_left _ _)
  have hratioOne : 1 < q.r0 / (q.K * q.delta |p₁|) := by
    rw [lt_div_iff₀ (mul_pos hKPos hdeltaPos)]
    simpa only [one_mul] using hsupport
  have hlogNonneg : 0 ≤ Real.log (q.r0 / (q.K * q.delta |p₁|)) :=
    (Real.log_pos hratioOne).le
  constructor
  · calc
      (1 / (4000 * Real.pi)) * q.scaleLog |p₁| ≤
          (2 * Real.pi)⁻¹ * ((1 / 4 : ℝ) *
            Real.log (q.r0 / (q.K * q.delta |p₁|))) := by
              have hpiPos := Real.pi_pos
              field_simp [Real.pi_ne_zero]
              nlinarith
      _ = (2 * Real.pi)⁻¹ *
          (∫ r in q.supportInterval |p₁|, (4 * r)⁻¹) := by rw [hlowerExact]
      _ ≤ _ := mul_le_mul_of_nonneg_left hlowerInt (by positivity)
  · calc
      (2 * Real.pi)⁻¹ *
          (∫ r in q.supportInterval |p₁|, mixedRadialKernel q r) ≤
          (2 * Real.pi)⁻¹ *
            (∫ r in q.supportInterval |p₁|, 2 * r⁻¹) :=
              mul_le_mul_of_nonneg_left hupperInt (by positivity)
      _ = Real.pi⁻¹ * Real.log (q.r0 / (q.K * q.delta |p₁|)) := by
        rw [hupperExact]
        field_simp [Real.pi_ne_zero]
      _ ≤ q.scaleLog |p₁| := by
        calc
          Real.pi⁻¹ * Real.log (q.r0 / (q.K * q.delta |p₁|)) ≤
              1 * q.scaleLog |p₁| := by
                exact mul_le_mul
                  ((inv_le_one₀ Real.pi_pos).2 (by linarith [Real.two_le_pi]))
                  hlogUpper hlogNonneg (by positivity)
          _ = _ := one_mul _

private theorem resolvent_periodic (mu : ℝ) :
    Function.Periodic (fun x : ℝ => (mu + dispersion x)⁻¹) (2 * Real.pi) := by
  intro x
  unfold dispersion
  change (mu + (1 - Real.cos (x + 2 * Real.pi)))⁻¹ =
    (mu + (1 - Real.cos x))⁻¹
  rw [Real.cos_add]
  simp

private theorem torusIntegral_add_of_periodic (f : ℝ → ℝ)
    (hf : Function.Periodic f (2 * Real.pi)) (c : ℝ) :
    torusIntegral (fun x : ℝ => f (x + c)) = torusIntegral f := by
  rw [torusIntegral, torusIntegral, torus,
    ← intervalIntegral.integral_of_le (le_of_lt (neg_lt_self Real.pi_pos)),
    ← intervalIntegral.integral_of_le (le_of_lt (neg_lt_self Real.pi_pos))]
  simp only [smul_eq_mul]
  rw [intervalIntegral.integral_comp_add_right]
  have hperiod := hf.intervalIntegral_add_eq (-Real.pi + c) (-Real.pi)
  have hinter : (∫ x in -Real.pi + c..Real.pi + c, f x) =
      ∫ x in -Real.pi..Real.pi, f x := by
    convert hperiod using 1 <;> ring_nf
  rw [hinter]

private theorem shiftedLineResolvent {q : Parameters} (hq : q.Admissible)
    (p₁ c : ℝ) :
    torusIntegral (fun x : ℝ =>
      (q.lambda + dispersion p₁ + dispersion (x + c))⁻¹) =
      (Real.sqrt ((q.lambda + dispersion p₁) *
        (q.lambda + dispersion p₁ + 2)))⁻¹ := by
  let mu : ℝ := q.lambda + dispersion p₁
  have hmu : 0 < mu := add_pos_of_pos_of_nonneg hq.1 (dispersion_nonneg p₁)
  calc
    torusIntegral (fun x : ℝ =>
        (q.lambda + dispersion p₁ + dispersion (x + c))⁻¹) =
        torusIntegral (fun x : ℝ => (mu + dispersion x)⁻¹) := by
          exact torusIntegral_add_of_periodic (fun x : ℝ =>
            (mu + dispersion x)⁻¹) (resolvent_periodic mu) c
    _ = _ := lineResolventIdentity_proved mu hmu

private theorem degreeOneCoefficientL2_le {q : Parameters} (hq : q.Admissible)
    {p₁ : ℝ} (hsinpNe : Real.sin p₁ ≠ 0)
    (hsupport : q.K * q.delta |p₁| < q.r0) :
    torusIntegral (fun r : ℝ => ‖degreeOneCoefficient q p₁ r‖ ^ 2) ≤
      (q.delta |p₁|)⁻¹ := by
  have hdeltaPos := successor_delta_pos hq (abs_nonneg p₁)
  have hKPos : 0 < q.K := by linarith [hq.2.2.1]
  have hleftPos : 0 < q.K * q.delta |p₁| := mul_pos hKPos hdeltaPos
  have hr0Pos := successor_r0_pos hq
  have hrightPi : q.r0 < Real.pi :=
    (successor_r0_le_pi_div_two hq).trans_lt (by linarith [Real.pi_pos])
  have hsignAbs : |Real.sign (Real.sin p₁)| = 1 := by
    rcases Real.sign_apply_eq_of_ne_zero (Real.sin p₁) hsinpNe with hsign | hsign
    · rw [hsign]
      norm_num
    · rw [hsign]
      norm_num
  have hcoeff : (fun r : ℝ => ‖degreeOneCoefficient q p₁ r‖ ^ 2) =
      fun r : ℝ => if r ∈ q.supportInterval |p₁| then
        (Real.sin r)⁻¹ ^ 2 else 0 := by
    funext r
    by_cases hr : r ∈ q.supportInterval |p₁|
    · simp only [degreeOneCoefficient, hr, if_pos, norm_div, norm_mul,
        norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        hsignAbs, one_div, one_mul, inv_pow, sq_abs]
    · simp [degreeOneCoefficient, hr]
  rw [hcoeff]
  have hsubset : q.supportInterval |p₁| ⊆ torus := by
    intro r hr
    exact ⟨(neg_lt_zero.mpr Real.pi_pos).trans (hleftPos.trans_le hr.1),
      hr.2.trans_lt hrightPi |>.le⟩
  rw [torusIntegral_indicator_real (s := q.supportInterval |p₁|)
    (fun r : ℝ => (Real.sin r)⁻¹ ^ 2) measurableSet_Icc hsubset]
  have hsinInvInt : IntegrableOn (fun r : ℝ => (Real.sin r)⁻¹ ^ 2)
      (q.supportInterval |p₁|) := by
    rw [Parameters.supportInterval]
    apply ContinuousOn.integrableOn_Icc
    apply ContinuousOn.pow
    apply ContinuousOn.inv₀ Real.continuous_sin.continuousOn
    intro r hr
    exact (Real.sin_pos_of_pos_of_lt_pi (hleftPos.trans_le hr.1)
      (hr.2.trans_lt hrightPi)).ne'
  have hpowInt : IntegrableOn (fun r : ℝ => 4 * r⁻¹ ^ 2)
      (q.supportInterval |p₁|) := by
    rw [Parameters.supportInterval]
    apply ContinuousOn.integrableOn_Icc
    exact continuousOn_const.mul ((ContinuousOn.inv₀ continuous_id.continuousOn
      (fun r hr => (hleftPos.trans_le hr.1).ne')).pow 2)
  have hpoint : ∀ r ∈ q.supportInterval |p₁|,
      (Real.sin r)⁻¹ ^ 2 ≤ 4 * r⁻¹ ^ 2 := by
    intro r hr
    have hrPos : 0 < r := hleftPos.trans_le hr.1
    have hrSmall : r ≤ Real.pi / 2 := hr.2.trans (successor_r0_le_pi_div_two hq)
    have hsinPos : 0 < Real.sin r := Real.sin_pos_of_pos_of_lt_pi hrPos
      (hrSmall.trans_lt (by linarith [Real.pi_pos]))
    have hjordan := Real.mul_abs_le_abs_sin
      (show |r| ≤ Real.pi / 2 by rw [abs_of_pos hrPos]; exact hrSmall)
    have hsinLower : r / 2 ≤ Real.sin r := by
      calc
        r / 2 = |r| / 2 := by rw [abs_of_pos hrPos]
        _ ≤ (2 / Real.pi) * |r| := by
          have hc : (1 / 2 : ℝ) ≤ 2 / Real.pi := by
            rw [le_div_iff₀ Real.pi_pos]
            nlinarith [Real.pi_le_four]
          simpa only [div_eq_mul_inv, one_mul, mul_comm] using
            mul_le_mul_of_nonneg_right hc (abs_nonneg r)
        _ ≤ |Real.sin r| := hjordan
        _ = Real.sin r := abs_of_pos hsinPos
    have hinv := (inv_le_inv₀ hsinPos (by linarith : 0 < r / 2)).2 hsinLower
    have hmajorantEq : (4 : ℝ) * r⁻¹ ^ 2 = (r / 2)⁻¹ ^ 2 := by
      field_simp
      norm_num
    rw [hmajorantEq]
    exact pow_le_pow_left₀ (inv_nonneg.mpr hsinPos.le) hinv 2
  have hmono : (∫ r in q.supportInterval |p₁|, (Real.sin r)⁻¹ ^ 2) ≤
      ∫ r in q.supportInterval |p₁|, 4 * r⁻¹ ^ 2 :=
    setIntegral_mono_on hsinInvInt hpowInt measurableSet_Icc hpoint
  have hzero : (0 : ℝ) ∉ Set.uIcc (q.K * q.delta |p₁|) q.r0 := by
    rw [uIcc_of_le hsupport.le]
    intro h
    exact (not_le_of_gt hleftPos) h.1
  have hzpow := integral_zpow (a := q.K * q.delta |p₁|) (b := q.r0)
    (n := (-2 : ℤ)) (Or.inr ⟨by norm_num, hzero⟩)
  norm_num [zpow_neg, div_eq_mul_inv] at hzpow
  have hinvSqIntegral : (∫ r in q.supportInterval |p₁|, r⁻¹ ^ 2) =
      (q.K * q.delta |p₁|)⁻¹ - q.r0⁻¹ := by
    rw [Parameters.supportInterval, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hsupport.le]
    simpa only [inv_pow, mul_inv_rev] using hzpow
  have hmajorant : (∫ r in q.supportInterval |p₁|, 4 * r⁻¹ ^ 2) ≤
      4 * (q.K * q.delta |p₁|)⁻¹ := by
    rw [integral_const_mul, hinvSqIntegral]
    have hr0InvNonneg : 0 ≤ q.r0⁻¹ := inv_nonneg.mpr hr0Pos.le
    nlinarith
  calc
    (2 * Real.pi)⁻¹ *
        (∫ r in q.supportInterval |p₁|, (Real.sin r)⁻¹ ^ 2) ≤
        (2 * Real.pi)⁻¹ * (4 * (q.K * q.delta |p₁|)⁻¹) :=
          mul_le_mul_of_nonneg_left (hmono.trans hmajorant) (by positivity)
    _ ≤ (q.delta |p₁|)⁻¹ := by
      have hfactor : (2 * Real.pi)⁻¹ *
          (4 * (q.K * q.delta |p₁|)⁻¹) =
          ((2 * Real.pi)⁻¹ * 4 * q.K⁻¹) * (q.delta |p₁|)⁻¹ := by
        field_simp [Real.pi_ne_zero, hKPos.ne', hdeltaPos.ne']
      rw [hfactor]
      have hc : (2 * Real.pi)⁻¹ * 4 * q.K⁻¹ ≤ 1 := by
        rw [← div_eq_mul_inv, div_le_iff₀ hKPos]
        field_simp [Real.pi_ne_zero]
        nlinarith [Real.two_le_pi, hq.2.2.1]
      calc
        (2 * Real.pi)⁻¹ * 4 * q.K⁻¹ * (q.delta |p₁|)⁻¹ ≤
            1 * (q.delta |p₁|)⁻¹ :=
          mul_le_mul_of_nonneg_right hc (inv_nonneg.mpr hdeltaPos.le)
        _ = _ := one_mul _

private theorem degreeOneCoefficient_norm_sq {q : Parameters} {p₁ r : ℝ}
    (hsinpNe : Real.sin p₁ ≠ 0) :
    ‖degreeOneCoefficient q p₁ r‖ ^ 2 =
      if r ∈ q.supportInterval |p₁| then (Real.sin r)⁻¹ ^ 2 else 0 := by
  have hsignAbs : |Real.sign (Real.sin p₁)| = 1 := by
    rcases Real.sign_apply_eq_of_ne_zero (Real.sin p₁) hsinpNe with hsign | hsign
    · rw [hsign]
      norm_num
    · rw [hsign]
      norm_num
  by_cases hr : r ∈ q.supportInterval |p₁|
  · simp only [degreeOneCoefficient, hr, if_pos, norm_div, norm_mul,
      norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      hsignAbs, one_div, one_mul, inv_pow, sq_abs]
  · simp [degreeOneCoefficient, hr]

private theorem degreeOneCoefficient_norm_sq_measurable {q : Parameters} {p₁ : ℝ}
    (hsinpNe : Real.sin p₁ ≠ 0) :
    Measurable (fun r : ℝ => ‖degreeOneCoefficient q p₁ r‖ ^ 2) := by
  simp_rw [degreeOneCoefficient_norm_sq hsinpNe]
  exact Measurable.ite measurableSet_Icc
    (Real.continuous_sin.measurable.inv.pow_const 2) measurable_const

private theorem degreeOneCoefficient_norm_sq_bound {q : Parameters} (hq : q.Admissible)
    {p₁ r : ℝ} (hsinpNe : Real.sin p₁ ≠ 0) :
    ‖degreeOneCoefficient q p₁ r‖ ^ 2 ≤
      4 * (q.K * q.delta |p₁|)⁻¹ ^ 2 := by
  rw [degreeOneCoefficient_norm_sq hsinpNe]
  by_cases hr : r ∈ q.supportInterval |p₁|
  · rw [if_pos hr]
    have hdeltaPos := successor_delta_pos hq (abs_nonneg p₁)
    have hleftPos : 0 < q.K * q.delta |p₁| :=
      mul_pos (by linarith [hq.2.2.1]) hdeltaPos
    have hrPos : 0 < r := hleftPos.trans_le hr.1
    have hrSmall : r ≤ Real.pi / 2 := hr.2.trans (successor_r0_le_pi_div_two hq)
    have hsinPos : 0 < Real.sin r := Real.sin_pos_of_pos_of_lt_pi hrPos
      (hrSmall.trans_lt (by linarith [Real.pi_pos]))
    have hjordan := Real.mul_abs_le_abs_sin
      (show |r| ≤ Real.pi / 2 by rw [abs_of_pos hrPos]; exact hrSmall)
    have hsinLower : r / 2 ≤ Real.sin r := by
      calc
        r / 2 = |r| / 2 := by rw [abs_of_pos hrPos]
        _ ≤ (2 / Real.pi) * |r| := by
          have hc : (1 / 2 : ℝ) ≤ 2 / Real.pi := by
            rw [le_div_iff₀ Real.pi_pos]
            nlinarith [Real.pi_le_four]
          simpa only [div_eq_mul_inv, one_mul, mul_comm] using
            mul_le_mul_of_nonneg_right hc (abs_nonneg r)
        _ ≤ |Real.sin r| := hjordan
        _ = Real.sin r := abs_of_pos hsinPos
    have hinvSin : (Real.sin r)⁻¹ ≤ (r / 2)⁻¹ :=
      (inv_le_inv₀ hsinPos (by linarith : 0 < r / 2)).2 hsinLower
    have hinvR : r⁻¹ ≤ (q.K * q.delta |p₁|)⁻¹ :=
      (inv_le_inv₀ hrPos hleftPos).2 hr.1
    have hsinSq : (Real.sin r)⁻¹ ^ 2 ≤ 4 * r⁻¹ ^ 2 := by
      have heq : (4 : ℝ) * r⁻¹ ^ 2 = (r / 2)⁻¹ ^ 2 := by
        field_simp
        norm_num
      rw [heq]
      exact pow_le_pow_left₀ (inv_nonneg.mpr hsinPos.le) hinvSin 2
    exact hsinSq.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (inv_nonneg.mpr hrPos.le) hinvR 2) (by norm_num))
  · rw [if_neg hr]
    positivity

private theorem twoRowWeight_measurable (q : Parameters) (p₁ p₂ : ℝ) :
    Measurable (fun z : ℝ × ℝ =>
      twoRowHMinusWeight q p₁ (z.1 + z.2 - p₂)) := by
  unfold twoRowHMinusWeight dispersion
  fun_prop

private theorem twoRowWeight_nonneg {q : Parameters} (hq : q.Admissible)
    (p₁ p₂ r r' : ℝ) :
    0 ≤ twoRowHMinusWeight q p₁ (r + r' - p₂) := by
  unfold twoRowHMinusWeight
  exact inv_nonneg.mpr (add_nonneg
    (add_nonneg hq.1.le (dispersion_nonneg p₁)) (dispersion_nonneg _))

private theorem twoRowWeight_le_inv_lambda {q : Parameters} (hq : q.Admissible)
    (p₁ p₂ r r' : ℝ) :
    twoRowHMinusWeight q p₁ (r + r' - p₂) ≤ q.lambda⁻¹ := by
  unfold twoRowHMinusWeight
  apply (inv_le_inv₀ (by
    exact add_pos_of_pos_of_nonneg
      (add_pos_of_pos_of_nonneg hq.1 (dispersion_nonneg p₁))
      (dispersion_nonneg _)) hq.1).2
  nlinarith [dispersion_nonneg p₁, dispersion_nonneg (r + r' - p₂)]

private theorem twoRowRadialKernel_le {q : Parameters} (hq : q.Admissible)
    {p₁ : ℝ} (hpTorus : p₁ ∈ torus) :
    (Real.sqrt ((q.lambda + dispersion p₁) *
      (q.lambda + dispersion p₁ + 2)))⁻¹ ≤ 4 * (q.delta |p₁|)⁻¹ := by
  have hpAbs : |p₁| ≤ Real.pi := by
    exact abs_le.2 ⟨hpTorus.1.le, hpTorus.2⟩
  have hdisp := (dispersion_quadratic_bounds hpAbs).1
  have hpiSq : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_pos, Real.pi_le_four]
  have hdispCoarse : p₁ ^ 2 / 8 ≤ dispersion p₁ := by
    have hquad : p₁ ^ 2 / 8 ≤ 2 * p₁ ^ 2 / Real.pi ^ 2 := by
      rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 8)
        (sq_pos_of_pos Real.pi_pos)]
      nlinarith [sq_nonneg p₁]
    exact hquad.trans hdisp
  let mu : ℝ := q.lambda + dispersion p₁
  have hmuPos : 0 < mu := add_pos_of_pos_of_nonneg hq.1 (dispersion_nonneg p₁)
  have hdeltaPos := successor_delta_pos hq (abs_nonneg p₁)
  have hsqrtSq : (Real.sqrt q.lambda) ^ 2 = q.lambda := Real.sq_sqrt hq.1.le
  have hdeltaSq : q.delta |p₁| ^ 2 ≤ 16 * mu := by
    rw [Parameters.delta]
    rw [← sq_abs p₁] at hdispCoarse
    dsimp [mu]
    nlinarith [Real.sqrt_nonneg q.lambda,
      mul_nonneg (Real.sqrt_nonneg q.lambda) (abs_nonneg p₁)]
  have hprodPos : 0 < mu * (mu + 2) := mul_pos hmuPos (by linarith)
  have hprodLower : (q.delta |p₁| / 4) ^ 2 ≤ mu * (mu + 2) := by
    nlinarith [mul_nonneg hmuPos.le (by linarith : 0 ≤ mu + 2)]
  have hrootLower : q.delta |p₁| / 4 ≤ Real.sqrt (mu * (mu + 2)) := by
    rw [← Real.sqrt_sq (by positivity : 0 ≤ q.delta |p₁| / 4)]
    exact Real.sqrt_le_sqrt hprodLower
  have hrootPos : 0 < Real.sqrt (mu * (mu + 2)) := Real.sqrt_pos.2 hprodPos
  calc
    (Real.sqrt (mu * (mu + 2)))⁻¹ ≤ (q.delta |p₁| / 4)⁻¹ :=
      (inv_le_inv₀ hrootPos (by positivity : 0 < q.delta |p₁| / 4)).2 hrootLower
    _ = 4 * (q.delta |p₁|)⁻¹ := by field_simp

private noncomputable def twoRowOriginal (q : Parameters) (p₁ p₂ : ℝ)
    (r r' : ℝ) : ℝ :=
  twoRowHMinusWeight q p₁ (r + r' - p₂) *
    ‖Complex.I * (Real.sin p₁ : ℂ) *
      (degreeOneCoefficient q p₁ r + degreeOneCoefficient q p₁ r')‖ ^ 2

private noncomputable def twoRowMajorant (q : Parameters) (p₁ p₂ : ℝ)
    (r r' : ℝ) : ℝ :=
  2 * Real.sin p₁ ^ 2 * twoRowHMinusWeight q p₁ (r + r' - p₂) *
    (‖degreeOneCoefficient q p₁ r‖ ^ 2 +
      ‖degreeOneCoefficient q p₁ r'‖ ^ 2)

private theorem degreeOneCoefficient_measurable {q : Parameters} {p₁ : ℝ} :
    Measurable (degreeOneCoefficient q p₁) := by
  unfold degreeOneCoefficient
  apply Measurable.ite measurableSet_Icc
  · fun_prop
  · exact measurable_const

private theorem twoRowOriginal_le_majorant (q : Parameters) (hq : q.Admissible)
    (p₁ p₂ r r' : ℝ) :
    twoRowOriginal q p₁ p₂ r r' ≤ twoRowMajorant q p₁ p₂ r r' := by
  have hwNonneg : 0 ≤ twoRowHMinusWeight q p₁ (r + r' - p₂) := by
    unfold twoRowHMinusWeight
    exact inv_nonneg.mpr (add_nonneg
      (add_nonneg hq.1.le
        (dispersion_nonneg p₁)) (dispersion_nonneg _))
  have hnormAdd : ‖degreeOneCoefficient q p₁ r + degreeOneCoefficient q p₁ r'‖ ^ 2 ≤
      2 * (‖degreeOneCoefficient q p₁ r‖ ^ 2 +
        ‖degreeOneCoefficient q p₁ r'‖ ^ 2) := by
    have htriangle := norm_add_le (degreeOneCoefficient q p₁ r)
      (degreeOneCoefficient q p₁ r')
    have hnormNonneg := norm_nonneg (degreeOneCoefficient q p₁ r +
      degreeOneCoefficient q p₁ r')
    have hsumNonneg : 0 ≤ ‖degreeOneCoefficient q p₁ r‖ +
        ‖degreeOneCoefficient q p₁ r'‖ := by positivity
    calc
      ‖degreeOneCoefficient q p₁ r + degreeOneCoefficient q p₁ r'‖ ^ 2 ≤
          (‖degreeOneCoefficient q p₁ r‖ +
            ‖degreeOneCoefficient q p₁ r'‖) ^ 2 :=
        pow_le_pow_left₀ hnormNonneg htriangle 2
      _ ≤ _ := by nlinarith [sq_nonneg (‖degreeOneCoefficient q p₁ r‖ -
        ‖degreeOneCoefficient q p₁ r'‖)]
  unfold twoRowOriginal twoRowMajorant
  have hscalar : ‖Complex.I * (Real.sin p₁ : ℂ) *
      (degreeOneCoefficient q p₁ r + degreeOneCoefficient q p₁ r')‖ ^ 2 =
      Real.sin p₁ ^ 2 *
        ‖degreeOneCoefficient q p₁ r + degreeOneCoefficient q p₁ r'‖ ^ 2 := by
    simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, mul_pow, sq_abs]
  rw [hscalar]
  calc
    twoRowHMinusWeight q p₁ (r + r' - p₂) *
        (Real.sin p₁ ^ 2 *
          ‖degreeOneCoefficient q p₁ r + degreeOneCoefficient q p₁ r'‖ ^ 2) ≤
        twoRowHMinusWeight q p₁ (r + r' - p₂) *
          (Real.sin p₁ ^ 2 * (2 * (‖degreeOneCoefficient q p₁ r‖ ^ 2 +
            ‖degreeOneCoefficient q p₁ r'‖ ^ 2))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hnormAdd (sq_nonneg (Real.sin p₁))) hwNonneg
    _ = _ := by ring

private theorem twoRowOriginal_integrable {q : Parameters} (hq : q.Admissible)
    {p₁ p₂ : ℝ} (hsinpNe : Real.sin p₁ ≠ 0) :
    Integrable (Function.uncurry (twoRowOriginal q p₁ p₂))
      ((volume.restrict torus).prod (volume.restrict torus)) := by
  letI : IsFiniteMeasure (volume.restrict torus) := ⟨by
    rw [Measure.restrict_apply_univ, torus]
    exact measure_Ioc_lt_top⟩
  have hmeas : Measurable (Function.uncurry (twoRowOriginal q p₁ p₂)) := by
    unfold Function.uncurry twoRowOriginal
    exact (twoRowWeight_measurable q p₁ p₂).mul
      (((measurable_const.mul measurable_const).mul
        (((degreeOneCoefficient_measurable.comp measurable_fst).add
          (degreeOneCoefficient_measurable.comp measurable_snd)))).norm.pow_const 2)
  let B : ℝ := 4 * (q.K * q.delta |p₁|)⁻¹ ^ 2
  apply Integrable.of_bound hmeas.aestronglyMeasurable (q.lambda⁻¹ * (4 * B))
  filter_upwards with z
  have hu := degreeOneCoefficient_norm_sq_bound hq hsinpNe (r := z.1)
  have hv := degreeOneCoefficient_norm_sq_bound hq hsinpNe (r := z.2)
  have hsum : ‖degreeOneCoefficient q p₁ z.1 + degreeOneCoefficient q p₁ z.2‖ ^ 2 ≤
      4 * B := by
    have htriangle := norm_add_le (degreeOneCoefficient q p₁ z.1)
      (degreeOneCoefficient q p₁ z.2)
    have hsq : ‖degreeOneCoefficient q p₁ z.1 + degreeOneCoefficient q p₁ z.2‖ ^ 2 ≤
        2 * (‖degreeOneCoefficient q p₁ z.1‖ ^ 2 +
          ‖degreeOneCoefficient q p₁ z.2‖ ^ 2) := by
      exact (pow_le_pow_left₀ (norm_nonneg _) htriangle 2).trans (by
        nlinarith [sq_nonneg (‖degreeOneCoefficient q p₁ z.1‖ -
          ‖degreeOneCoefficient q p₁ z.2‖)])
    dsimp [B] at hu hv ⊢
    nlinarith
  have hscalar : ‖Complex.I * (Real.sin p₁ : ℂ) *
      (degreeOneCoefficient q p₁ z.1 + degreeOneCoefficient q p₁ z.2)‖ ^ 2 ≤
      4 * B := by
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, mul_pow, sq_abs]
    have hsinSq : Real.sin p₁ ^ 2 ≤ 1 := Real.sin_sq_le_one p₁
    exact (mul_le_mul_of_nonneg_left hsum (sq_nonneg _)).trans (by
      dsimp [B]
      nlinarith [show 0 ≤ 4 * (q.K * q.delta |p₁|)⁻¹ ^ 2 by positivity])
  have hw := twoRowWeight_le_inv_lambda hq p₁ p₂ z.1 z.2
  have hwNonneg := twoRowWeight_nonneg hq p₁ p₂ z.1 z.2
  change |twoRowOriginal q p₁ p₂ z.1 z.2| ≤ q.lambda⁻¹ * (4 * B)
  rw [twoRowOriginal, abs_of_nonneg (mul_nonneg hwNonneg (sq_nonneg _))]
  exact mul_le_mul hw hscalar (by positivity) (inv_nonneg.mpr hq.1.le)

private theorem twoRowMajorant_integrable {q : Parameters} (hq : q.Admissible)
    {p₁ p₂ : ℝ} (hsinpNe : Real.sin p₁ ≠ 0) :
    Integrable (Function.uncurry (twoRowMajorant q p₁ p₂))
      ((volume.restrict torus).prod (volume.restrict torus)) := by
  letI : IsFiniteMeasure (volume.restrict torus) := ⟨by
    rw [Measure.restrict_apply_univ, torus]
    exact measure_Ioc_lt_top⟩
  have huMeas := degreeOneCoefficient_norm_sq_measurable (q := q) hsinpNe
  have hmeas : Measurable (Function.uncurry (twoRowMajorant q p₁ p₂)) := by
    unfold Function.uncurry twoRowMajorant
    exact (((measurable_const.mul measurable_const).mul
      (twoRowWeight_measurable q p₁ p₂)).mul
      ((huMeas.comp measurable_fst).add (huMeas.comp measurable_snd)))
  let B : ℝ := 4 * (q.K * q.delta |p₁|)⁻¹ ^ 2
  apply Integrable.of_bound hmeas.aestronglyMeasurable
    (2 * Real.sin p₁ ^ 2 * q.lambda⁻¹ * (2 * B))
  filter_upwards with z
  have hu := degreeOneCoefficient_norm_sq_bound hq hsinpNe (r := z.1)
  have hv := degreeOneCoefficient_norm_sq_bound hq hsinpNe (r := z.2)
  have hw := twoRowWeight_le_inv_lambda hq p₁ p₂ z.1 z.2
  have hwNonneg := twoRowWeight_nonneg hq p₁ p₂ z.1 z.2
  have hvalueNonneg : 0 ≤ twoRowMajorant q p₁ p₂ z.1 z.2 := by
    unfold twoRowMajorant
    positivity
  change |twoRowMajorant q p₁ p₂ z.1 z.2| ≤
    2 * Real.sin p₁ ^ 2 * q.lambda⁻¹ * (2 * B)
  rw [abs_of_nonneg hvalueNonneg]
  unfold twoRowMajorant
  dsimp [B] at hu hv ⊢
  have hsum : ‖degreeOneCoefficient q p₁ z.1‖ ^ 2 +
      ‖degreeOneCoefficient q p₁ z.2‖ ^ 2 ≤
      2 * (4 * (q.K * q.delta |p₁|)⁻¹ ^ 2) := by linarith
  have hbase : twoRowHMinusWeight q p₁ (z.1 + z.2 - p₂) *
      (‖degreeOneCoefficient q p₁ z.1‖ ^ 2 +
        ‖degreeOneCoefficient q p₁ z.2‖ ^ 2) ≤
      q.lambda⁻¹ * (2 * (4 * (q.K * q.delta |p₁|)⁻¹ ^ 2)) :=
    mul_le_mul hw hsum (by positivity) (inv_nonneg.mpr hq.1.le)
  calc
    2 * Real.sin p₁ ^ 2 * twoRowHMinusWeight q p₁ (z.1 + z.2 - p₂) *
        (‖degreeOneCoefficient q p₁ z.1‖ ^ 2 +
          ‖degreeOneCoefficient q p₁ z.2‖ ^ 2) =
        (2 * Real.sin p₁ ^ 2) *
          (twoRowHMinusWeight q p₁ (z.1 + z.2 - p₂) *
            (‖degreeOneCoefficient q p₁ z.1‖ ^ 2 +
              ‖degreeOneCoefficient q p₁ z.2‖ ^ 2)) := by ring
    _ ≤ (2 * Real.sin p₁ ^ 2) *
        (q.lambda⁻¹ * (2 * (4 * (q.K * q.delta |p₁|)⁻¹ ^ 2))) :=
      mul_le_mul_of_nonneg_left hbase
        (mul_nonneg (by norm_num) (sq_nonneg _))
    _ = _ := by ring

private theorem torusIntegral₂_eq_prodIntegral (F : ℝ → ℝ → ℝ)
    (hF : Integrable (Function.uncurry F)
      ((volume.restrict torus).prod (volume.restrict torus))) :
    torusIntegral (fun r : ℝ => torusIntegral (fun r' : ℝ => F r r')) =
      (2 * Real.pi)⁻¹ ^ 2 *
        ∫ z, Function.uncurry F z ∂((volume.restrict torus).prod
          (volume.restrict torus)) := by
  rw [torusIntegral]
  simp only [smul_eq_mul, torusIntegral, integral_const_mul]
  rw [integral_integral hF]
  change (2 * Real.pi)⁻¹ * ((2 * Real.pi)⁻¹ *
      ∫ z, Function.uncurry F z ∂((volume.restrict torus).prod
        (volume.restrict torus))) =
    (2 * Real.pi)⁻¹ ^ 2 *
      ∫ z, Function.uncurry F z ∂((volume.restrict torus).prod
        (volume.restrict torus))
  ring

private theorem torusIntegral₂_swap (F : ℝ → ℝ → ℝ)
    (hF : Integrable (Function.uncurry F)
      ((volume.restrict torus).prod (volume.restrict torus))) :
    torusIntegral (fun r : ℝ => torusIntegral (fun r' : ℝ => F r r')) =
      torusIntegral (fun r' : ℝ => torusIntegral (fun r : ℝ => F r r')) := by
  simp only [torusIntegral, smul_eq_mul, integral_const_mul]
  rw [integral_integral_swap hF]

private noncomputable def twoRowLeft (q : Parameters) (p₁ p₂ : ℝ)
    (r r' : ℝ) : ℝ :=
  twoRowHMinusWeight q p₁ (r + r' - p₂) *
    ‖degreeOneCoefficient q p₁ r‖ ^ 2

private noncomputable def twoRowRight (q : Parameters) (p₁ p₂ : ℝ)
    (r r' : ℝ) : ℝ :=
  twoRowHMinusWeight q p₁ (r + r' - p₂) *
    ‖degreeOneCoefficient q p₁ r'‖ ^ 2

private theorem twoRowLeft_integrable {q : Parameters} (hq : q.Admissible)
    {p₁ p₂ : ℝ} (hsinpNe : Real.sin p₁ ≠ 0) :
    Integrable (Function.uncurry (twoRowLeft q p₁ p₂))
      ((volume.restrict torus).prod (volume.restrict torus)) := by
  letI : IsFiniteMeasure (volume.restrict torus) := ⟨by
    rw [Measure.restrict_apply_univ, torus]
    exact measure_Ioc_lt_top⟩
  have huMeas := degreeOneCoefficient_norm_sq_measurable (q := q) hsinpNe
  have hmeas : Measurable (Function.uncurry (twoRowLeft q p₁ p₂)) := by
    unfold Function.uncurry twoRowLeft
    exact (twoRowWeight_measurable q p₁ p₂).mul (huMeas.comp measurable_fst)
  let B : ℝ := 4 * (q.K * q.delta |p₁|)⁻¹ ^ 2
  apply Integrable.of_bound hmeas.aestronglyMeasurable (q.lambda⁻¹ * B)
  filter_upwards with z
  have hu := degreeOneCoefficient_norm_sq_bound hq hsinpNe (r := z.1)
  have hw := twoRowWeight_le_inv_lambda hq p₁ p₂ z.1 z.2
  have hwNonneg := twoRowWeight_nonneg hq p₁ p₂ z.1 z.2
  have hvalueNonneg : 0 ≤ twoRowLeft q p₁ p₂ z.1 z.2 := by
    unfold twoRowLeft
    positivity
  change |twoRowLeft q p₁ p₂ z.1 z.2| ≤ q.lambda⁻¹ * B
  rw [abs_of_nonneg hvalueNonneg]
  unfold twoRowLeft
  dsimp [B] at hu ⊢
  exact mul_le_mul hw hu (sq_nonneg _) (inv_nonneg.mpr hq.1.le)

private theorem twoRowRight_integrable {q : Parameters} (hq : q.Admissible)
    {p₁ p₂ : ℝ} (hsinpNe : Real.sin p₁ ≠ 0) :
    Integrable (Function.uncurry (twoRowRight q p₁ p₂))
      ((volume.restrict torus).prod (volume.restrict torus)) := by
  letI : IsFiniteMeasure (volume.restrict torus) := ⟨by
    rw [Measure.restrict_apply_univ, torus]
    exact measure_Ioc_lt_top⟩
  have huMeas := degreeOneCoefficient_norm_sq_measurable (q := q) hsinpNe
  have hmeas : Measurable (Function.uncurry (twoRowRight q p₁ p₂)) := by
    unfold Function.uncurry twoRowRight
    exact (twoRowWeight_measurable q p₁ p₂).mul (huMeas.comp measurable_snd)
  let B : ℝ := 4 * (q.K * q.delta |p₁|)⁻¹ ^ 2
  apply Integrable.of_bound hmeas.aestronglyMeasurable (q.lambda⁻¹ * B)
  filter_upwards with z
  have hu := degreeOneCoefficient_norm_sq_bound hq hsinpNe (r := z.2)
  have hw := twoRowWeight_le_inv_lambda hq p₁ p₂ z.1 z.2
  have hwNonneg := twoRowWeight_nonneg hq p₁ p₂ z.1 z.2
  have hvalueNonneg : 0 ≤ twoRowRight q p₁ p₂ z.1 z.2 := by
    unfold twoRowRight
    positivity
  change |twoRowRight q p₁ p₂ z.1 z.2| ≤ q.lambda⁻¹ * B
  rw [abs_of_nonneg hvalueNonneg]
  unfold twoRowRight
  dsimp [B] at hu ⊢
  exact mul_le_mul hw hu (sq_nonneg _) (inv_nonneg.mpr hq.1.le)

private theorem twoRowLeft_integral_eq {q : Parameters} (hq : q.Admissible)
    (p₁ p₂ : ℝ) :
    torusIntegral (fun r : ℝ => torusIntegral (fun r' : ℝ =>
      twoRowLeft q p₁ p₂ r r')) =
      (Real.sqrt ((q.lambda + dispersion p₁) *
        (q.lambda + dispersion p₁ + 2)))⁻¹ *
        torusIntegral (fun r : ℝ => ‖degreeOneCoefficient q p₁ r‖ ^ 2) := by
  let R : ℝ := (Real.sqrt ((q.lambda + dispersion p₁) *
    (q.lambda + dispersion p₁ + 2)))⁻¹
  have hinner : (fun r : ℝ => torusIntegral (fun r' : ℝ =>
      twoRowLeft q p₁ p₂ r r')) =
      fun r : ℝ => ‖degreeOneCoefficient q p₁ r‖ ^ 2 * R := by
    funext r
    calc
      torusIntegral (fun r' : ℝ => twoRowLeft q p₁ p₂ r r') =
          ‖degreeOneCoefficient q p₁ r‖ ^ 2 *
            torusIntegral (fun r' : ℝ =>
              (q.lambda + dispersion p₁ + dispersion (r' + (r - p₂)))⁻¹) := by
        rw [← successor_torusIntegral_const_mul]
        apply congrArg torusIntegral
        funext r'
        unfold twoRowLeft twoRowHMinusWeight
        ring_nf
      _ = ‖degreeOneCoefficient q p₁ r‖ ^ 2 * R := by
        rw [shiftedLineResolvent hq p₁ (r - p₂)]
  rw [hinner]
  calc
    torusIntegral (fun r : ℝ => ‖degreeOneCoefficient q p₁ r‖ ^ 2 * R) =
        torusIntegral (fun r : ℝ => R * ‖degreeOneCoefficient q p₁ r‖ ^ 2) := by
      apply congrArg torusIntegral
      funext r
      ring
    _ = R * torusIntegral (fun r : ℝ => ‖degreeOneCoefficient q p₁ r‖ ^ 2) :=
      successor_torusIntegral_const_mul R _

private theorem twoRowRight_integral_eq_left {q : Parameters} (hq : q.Admissible)
    {p₁ p₂ : ℝ} (hsinpNe : Real.sin p₁ ≠ 0) :
    torusIntegral (fun r : ℝ => torusIntegral (fun r' : ℝ =>
      twoRowRight q p₁ p₂ r r')) =
      torusIntegral (fun r : ℝ => torusIntegral (fun r' : ℝ =>
        twoRowLeft q p₁ p₂ r r')) := by
  calc
    torusIntegral (fun r : ℝ => torusIntegral (fun r' : ℝ =>
        twoRowRight q p₁ p₂ r r')) =
        torusIntegral (fun r' : ℝ => torusIntegral (fun r : ℝ =>
          twoRowRight q p₁ p₂ r r')) :=
      torusIntegral₂_swap (twoRowRight q p₁ p₂)
        (twoRowRight_integrable hq hsinpNe)
    _ = _ := by
      apply congrArg torusIntegral
      funext r'
      apply congrArg torusIntegral
      funext r
      unfold twoRowRight twoRowLeft
      congr 2
      ring

private theorem twoRowMajorant_integral_eq {q : Parameters} (hq : q.Admissible)
    {p₁ p₂ : ℝ} (hsinpNe : Real.sin p₁ ≠ 0) :
    torusIntegral (fun r : ℝ => torusIntegral (fun r' : ℝ =>
      twoRowMajorant q p₁ p₂ r r')) =
      4 * Real.sin p₁ ^ 2 *
        (Real.sqrt ((q.lambda + dispersion p₁) *
          (q.lambda + dispersion p₁ + 2)))⁻¹ *
        torusIntegral (fun r : ℝ => ‖degreeOneCoefficient q p₁ r‖ ^ 2) := by
  have hM := twoRowMajorant_integrable hq (p₂ := p₂) hsinpNe
  have hL := twoRowLeft_integrable hq (p₂ := p₂) hsinpNe
  have hR := twoRowRight_integrable hq (p₂ := p₂) hsinpNe
  rw [torusIntegral₂_eq_prodIntegral (twoRowMajorant q p₁ p₂) hM]
  have hpoint : Function.uncurry (twoRowMajorant q p₁ p₂) = fun z : ℝ × ℝ =>
      2 * Real.sin p₁ ^ 2 *
        (Function.uncurry (twoRowLeft q p₁ p₂) z +
          Function.uncurry (twoRowRight q p₁ p₂) z) := by
    funext z
    unfold Function.uncurry twoRowMajorant twoRowLeft twoRowRight
    ring
  rw [hpoint, integral_const_mul, integral_add hL hR]
  let R : ℝ := (Real.sqrt ((q.lambda + dispersion p₁) *
    (q.lambda + dispersion p₁ + 2)))⁻¹
  let U : ℝ := torusIntegral (fun r : ℝ => ‖degreeOneCoefficient q p₁ r‖ ^ 2)
  have hleftValue : torusIntegral (fun r : ℝ => torusIntegral (fun r' : ℝ =>
      twoRowLeft q p₁ p₂ r r')) = R * U := twoRowLeft_integral_eq hq p₁ p₂
  have hprodLeft : (2 * Real.pi)⁻¹ ^ 2 *
      (∫ z, Function.uncurry (twoRowLeft q p₁ p₂) z ∂
        ((volume.restrict torus).prod (volume.restrict torus))) = R * U :=
    (torusIntegral₂_eq_prodIntegral (twoRowLeft q p₁ p₂) hL).symm.trans hleftValue
  have hprodRight : (2 * Real.pi)⁻¹ ^ 2 *
      (∫ z, Function.uncurry (twoRowRight q p₁ p₂) z ∂
        ((volume.restrict torus).prod (volume.restrict torus))) = R * U :=
    (torusIntegral₂_eq_prodIntegral (twoRowRight q p₁ p₂) hR).symm.trans
      ((twoRowRight_integral_eq_left hq hsinpNe).trans hleftValue)
  calc
    (2 * Real.pi)⁻¹ ^ 2 *
        (2 * Real.sin p₁ ^ 2 *
          ((∫ z, Function.uncurry (twoRowLeft q p₁ p₂) z ∂
              ((volume.restrict torus).prod (volume.restrict torus))) +
            ∫ z, Function.uncurry (twoRowRight q p₁ p₂) z ∂
              ((volume.restrict torus).prod (volume.restrict torus)))) =
        2 * Real.sin p₁ ^ 2 *
          ((2 * Real.pi)⁻¹ ^ 2 *
              (∫ z, Function.uncurry (twoRowLeft q p₁ p₂) z ∂
                ((volume.restrict torus).prod (volume.restrict torus))) +
            (2 * Real.pi)⁻¹ ^ 2 *
              (∫ z, Function.uncurry (twoRowRight q p₁ p₂) z ∂
                ((volume.restrict torus).prod (volume.restrict torus)))) := by ring
    _ = 2 * Real.sin p₁ ^ 2 * (R * U + R * U) := by rw [hprodLeft, hprodRight]
    _ = 4 * Real.sin p₁ ^ 2 * R * U := by ring

private theorem twoRowResidualHMinusSq_le {q : Parameters} (hq : q.Admissible)
    {p₁ p₂ : ℝ} (hpTorus : p₁ ∈ torus) (hsinpNe : Real.sin p₁ ≠ 0)
    (hsupport : q.K * q.delta |p₁| < q.r0) :
    twoRowResidualHMinusSq q p₁ p₂ (degreeOneCoefficient q p₁) ≤ 16 := by
  have hO := twoRowOriginal_integrable hq (p₂ := p₂) hsinpNe
  have hM := twoRowMajorant_integrable hq (p₂ := p₂) hsinpNe
  have hprodMono : (∫ z, Function.uncurry (twoRowOriginal q p₁ p₂) z ∂
      ((volume.restrict torus).prod (volume.restrict torus))) ≤
      ∫ z, Function.uncurry (twoRowMajorant q p₁ p₂) z ∂
        ((volume.restrict torus).prod (volume.restrict torus)) := by
    apply integral_mono hO hM
    intro z
    exact twoRowOriginal_le_majorant q hq p₁ p₂ z.1 z.2
  have htorusMono : torusIntegral (fun r : ℝ => torusIntegral (fun r' : ℝ =>
      twoRowOriginal q p₁ p₂ r r')) ≤
      torusIntegral (fun r : ℝ => torusIntegral (fun r' : ℝ =>
        twoRowMajorant q p₁ p₂ r r')) := by
    rw [torusIntegral₂_eq_prodIntegral (twoRowOriginal q p₁ p₂) hO,
      torusIntegral₂_eq_prodIntegral (twoRowMajorant q p₁ p₂) hM]
    exact mul_le_mul_of_nonneg_left hprodMono (sq_nonneg _)
  rw [twoRowResidualHMinusSq]
  change torusIntegral (fun r : ℝ => torusIntegral (fun r' : ℝ =>
    twoRowOriginal q p₁ p₂ r r')) ≤ 16
  calc
    torusIntegral (fun r : ℝ => torusIntegral (fun r' : ℝ =>
        twoRowOriginal q p₁ p₂ r r')) ≤
        torusIntegral (fun r : ℝ => torusIntegral (fun r' : ℝ =>
          twoRowMajorant q p₁ p₂ r r')) := htorusMono
    _ = 4 * Real.sin p₁ ^ 2 *
        (Real.sqrt ((q.lambda + dispersion p₁) *
          (q.lambda + dispersion p₁ + 2)))⁻¹ *
        torusIntegral (fun r : ℝ => ‖degreeOneCoefficient q p₁ r‖ ^ 2) :=
      twoRowMajorant_integral_eq hq hsinpNe
    _ ≤ 16 := by
      let R : ℝ := (Real.sqrt ((q.lambda + dispersion p₁) *
        (q.lambda + dispersion p₁ + 2)))⁻¹
      let U : ℝ := torusIntegral (fun r : ℝ => ‖degreeOneCoefficient q p₁ r‖ ^ 2)
      have hdeltaPos := successor_delta_pos hq (abs_nonneg p₁)
      have hR : R ≤ 4 * (q.delta |p₁|)⁻¹ := twoRowRadialKernel_le hq hpTorus
      have hU : U ≤ (q.delta |p₁|)⁻¹ := degreeOneCoefficientL2_le hq hsinpNe hsupport
      have hRNonneg : 0 ≤ R := by
        dsimp [R]
        positivity
      have hUNonneg : 0 ≤ U := by
        dsimp [U]
        rw [torusIntegral]
        exact mul_nonneg (by positivity) (integral_nonneg fun r => sq_nonneg _)
      have hRU : R * U ≤
          (4 * (q.delta |p₁|)⁻¹) * (q.delta |p₁|)⁻¹ :=
        mul_le_mul hR hU hUNonneg (by positivity)
      have hpDelta : |p₁| ≤ q.delta |p₁| := by
        rw [Parameters.delta]
        exact le_add_of_nonneg_left (Real.sqrt_nonneg _)
      have hsinDeltaSq : Real.sin p₁ ^ 2 ≤ q.delta |p₁| ^ 2 := by
        calc
          Real.sin p₁ ^ 2 ≤ p₁ ^ 2 := Real.sin_sq_le_sq
          _ = |p₁| ^ 2 := (sq_abs p₁).symm
          _ ≤ q.delta |p₁| ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg p₁) hpDelta 2
      have hratio : Real.sin p₁ ^ 2 * (q.delta |p₁|)⁻¹ ^ 2 ≤ 1 := by
        rw [inv_pow, mul_inv_le_iff₀ (sq_pos_of_pos hdeltaPos)]
        simpa only [one_mul] using hsinDeltaSq
      calc
        4 * Real.sin p₁ ^ 2 * R * U =
            4 * Real.sin p₁ ^ 2 * (R * U) := by ring
        _ ≤ 4 * Real.sin p₁ ^ 2 *
            ((4 * (q.delta |p₁|)⁻¹) * (q.delta |p₁|)⁻¹) :=
          mul_le_mul_of_nonneg_left hRU
            (mul_nonneg (by norm_num) (sq_nonneg _))
        _ = 16 * (Real.sin p₁ ^ 2 * (q.delta |p₁|)⁻¹ ^ 2) := by ring
        _ ≤ 16 * 1 := mul_le_mul_of_nonneg_left hratio (by norm_num)
        _ = 16 := mul_one _

/-- Provider for the corrected successor of Lemma 4.1. The only change from
the frozen v1 statement is the application-side hypothesis `0 < |p₁|`.
The uniform witnesses are `c = 1 / (4000π)` and `C = 200000`. -/
theorem lemmaFourTwoSuccessorClaim_proved (K rho : ℝ) :
    LemmaFourTwoSuccessorClaim K rho := by
  intro hK hrhoPos hrhoUpper
  refine ⟨1 / (4000 * Real.pi), 200000, by positivity, by norm_num, ?_⟩
  intro lambda hlambdaPos hlambdaUpper p₁ p₂ hp₁Torus hp₂Torus hpOrder hpPos
  let q : Parameters := ⟨lambda, K, rho⟩
  change q.logThreshold < q.scaleLog |p₁| → _
  intro hlog
  have hq : q.Admissible :=
    ⟨hlambdaPos, hlambdaUpper, hK, hrhoPos, hrhoUpper⟩
  obtain ⟨hsupport, hscale, hlogInterval⟩ :=
    oneCoin_regime hq (abs_nonneg p₁) hlog
  have hdeltaPos := successor_delta_pos hq (abs_nonneg p₁)
  have hleft : 0 < q.K * q.delta |p₁| :=
    mul_pos (by linarith [hq.2.2.1]) hdeltaPos
  have hright : q.r0 < Real.pi :=
    (successor_r0_le_pi_div_two hq).trans_lt (by linarith [Real.pi_pos])
  have hpDelta : |p₁| ≤ q.delta |p₁| := by
    rw [Parameters.delta]
    exact le_add_of_nonneg_left (Real.sqrt_nonneg _)
  have hpR0 : |p₁| < q.r0 := by
    have hKOne : 1 ≤ q.K := by linarith [hq.2.2.1]
    exact hpDelta.trans (by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hKOne hdeltaPos.le) |>.trans_lt hsupport
  have hpSmall : |p₁| ≤ Real.pi / 2 :=
    hpR0.le.trans (successor_r0_le_pi_div_two hq)
  have hsinpNe : Real.sin p₁ ≠ 0 := by
    have hpAbsPi : |p₁| < Real.pi := hpSmall.trans_lt (by linarith [Real.pi_pos])
    rcases lt_or_gt_of_ne (abs_pos.mp hpPos) with hpNeg | hpRawPos
    · exact (Real.sin_neg_of_neg_of_neg_pi_lt hpNeg
        ((neg_lt_neg hpAbsPi).trans_le (neg_abs_le p₁))).ne
    · exact (Real.sin_pos_of_pos_of_lt_pi hpRawPos
        ((le_abs_self p₁).trans_lt hpAbsPi)).ne'
  have hmixed := mixedResidualHMinusSq_bounds hq hpPos hsupport hscale hlogInterval
  have hscalePos : 0 < q.scaleLog |p₁| := by
    rw [Parameters.scaleLog]
    exact add_pos_of_pos_of_nonneg zero_lt_one (le_max_left _ _)
  refine ⟨degreeZeroAdjoint_degreeOneCoefficient,
    degreeOneNormalization_lower hq hpPos hsupport hlogInterval, ?_, ?_,
    hmixed.1, ?_, ?_⟩
  · exact (degreeOneEnergy_le hq hpPos hsupport).trans (by norm_num)
  · intro r
    exact mixedResidual_eq_indicator hleft hright
  · exact hmixed.2.trans (by
      have hC : (1 : ℝ) ≤ 200000 := by norm_num
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hC hscalePos.le)
  · exact (twoRowResidualHMinusSq_le hq hp₁Torus hsinpNe hsupport).trans
      (by norm_num)

/-- The integrand defining the degree-one `H₁` energy. -/
noncomputable def degreeOneEnergyIntegrand (q : Parameters) (p₁ r : ℝ) : ℝ :=
  (q.lambda + dispersion p₁ + dispersion r) * ‖degreeOneCoefficient q p₁ r‖ ^ 2

/-- The product-space integrand defining the mixed squared `H⁻¹` norm. -/
noncomputable def mixedResidualHMinusIntegrand (q : Parameters) (p₁ : ℝ)
    (z : ℝ × ℝ) : ℝ :=
  mixedHMinusWeight q z.1 z.2 * ‖mixedResidual q p₁ z.1‖ ^ 2

/-- The product-space integrand defining the two-row squared `H⁻¹` norm. -/
noncomputable def twoRowResidualHMinusIntegrand (q : Parameters) (p₁ p₂ : ℝ)
    (z : ℝ × ℝ) : ℝ :=
  let alpha := z.1 + z.2 - p₂
  twoRowHMinusWeight q p₁ alpha *
    ‖Complex.I * (Real.sin p₁ : ℂ) *
      (degreeOneCoefficient q p₁ z.1 + degreeOneCoefficient q p₁ z.2)‖ ^ 2

/-- Finiteness certificate for every integral used as an energy or squared
`H⁻¹` norm in Lemma 4.1. The final two fields identify the iterated
normalized integrals with genuine finite product integrals. -/
structure LemmaFourTwoIntegralCertificate (q : Parameters) (p₁ p₂ : ℝ) : Prop where
  degreeOneEnergy_measurable : Measurable (degreeOneEnergyIntegrand q p₁)
  degreeOneEnergy_integrable :
    Integrable (degreeOneEnergyIntegrand q p₁) (volume.restrict torus)
  mixedHMinus_measurable : Measurable (mixedResidualHMinusIntegrand q p₁)
  mixedHMinus_integrable : Integrable (mixedResidualHMinusIntegrand q p₁)
    ((volume.restrict torus).prod (volume.restrict torus))
  twoRowHMinus_measurable : Measurable (twoRowResidualHMinusIntegrand q p₁ p₂)
  twoRowHMinus_integrable : Integrable (twoRowResidualHMinusIntegrand q p₁ p₂)
    ((volume.restrict torus).prod (volume.restrict torus))
  mixedHMinus_eq_finiteProductIntegral :
    mixedResidualHMinusSq q p₁ = (2 * Real.pi)⁻¹ ^ 2 *
      ∫ z, mixedResidualHMinusIntegrand q p₁ z ∂
        ((volume.restrict torus).prod (volume.restrict torus))
  twoRowHMinus_eq_finiteProductIntegral :
    twoRowResidualHMinusSq q p₁ p₂ (degreeOneCoefficient q p₁) =
      (2 * Real.pi)⁻¹ ^ 2 *
        ∫ z, twoRowResidualHMinusIntegrand q p₁ p₂ z ∂
          ((volume.restrict torus).prod (volume.restrict torus))

private theorem dispersion_le_two (s : ℝ) : dispersion s ≤ 2 := by
  unfold dispersion
  linarith [Real.neg_one_le_cos s]

private theorem mixedResidual_norm_sq_le_one {q : Parameters} {p₁ r : ℝ}
    (hsinpNe : Real.sin p₁ ≠ 0) (hleft : 0 < q.K * q.delta |p₁|)
    (hright : q.r0 < Real.pi) : ‖mixedResidual q p₁ r‖ ^ 2 ≤ 1 := by
  rw [mixedResidual_eq_indicator hleft hright]
  by_cases hr : r ∈ q.supportInterval |p₁|
  · have hsignAbs : |Real.sign (Real.sin p₁)| = 1 := by
      rcases Real.sign_apply_eq_of_ne_zero (Real.sin p₁) hsinpNe with hsign | hsign
      · rw [hsign]
        norm_num
      · rw [hsign]
        norm_num
    simp [signedSupportIndicator, hr, hsignAbs]
  · simp [signedSupportIndicator, hr]

/-- The explicit integral certificate used by the version-3 Lemma 4.1
successor. -/
theorem lemmaFourTwoIntegralCertificate_proved {q : Parameters} (hq : q.Admissible)
    {p₁ p₂ : ℝ} (hpPos : 0 < |p₁|)
    (hsupport : q.K * q.delta |p₁| < q.r0) :
    LemmaFourTwoIntegralCertificate q p₁ p₂ := by
  have hdeltaPos := successor_delta_pos hq (abs_nonneg p₁)
  have hleft : 0 < q.K * q.delta |p₁| :=
    mul_pos (by linarith [hq.2.2.1]) hdeltaPos
  have hright : q.r0 < Real.pi :=
    (successor_r0_le_pi_div_two hq).trans_lt (by linarith [Real.pi_pos])
  have hpDelta : |p₁| ≤ q.delta |p₁| := by
    rw [Parameters.delta]
    exact le_add_of_nonneg_left (Real.sqrt_nonneg _)
  have hpR0 : |p₁| < q.r0 := by
    have hKOne : 1 ≤ q.K := by linarith [hq.2.2.1]
    exact hpDelta.trans (by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hKOne hdeltaPos.le) |>.trans_lt hsupport
  have hpSmall : |p₁| ≤ Real.pi / 2 :=
    hpR0.le.trans (successor_r0_le_pi_div_two hq)
  have hsinpNe : Real.sin p₁ ≠ 0 := by
    have hpAbsPi : |p₁| < Real.pi := hpSmall.trans_lt (by linarith [Real.pi_pos])
    rcases lt_or_gt_of_ne (abs_pos.mp hpPos) with hpNeg | hpRawPos
    · exact (Real.sin_neg_of_neg_of_neg_pi_lt hpNeg
        ((neg_lt_neg hpAbsPi).trans_le (neg_abs_le p₁))).ne
    · exact (Real.sin_pos_of_pos_of_lt_pi hpRawPos
        ((le_abs_self p₁).trans_lt hpAbsPi)).ne'
  have henergyMeasurable : Measurable (degreeOneEnergyIntegrand q p₁) := by
    unfold degreeOneEnergyIntegrand
    have hw : Measurable (fun r : ℝ =>
        q.lambda + dispersion p₁ + dispersion r) := by
      unfold dispersion
      fun_prop
    exact hw.mul (degreeOneCoefficient_measurable.norm.pow_const 2)
  have henergyIntegrable : Integrable (degreeOneEnergyIntegrand q p₁)
      (volume.restrict torus) := by
    letI : IsFiniteMeasure (volume.restrict torus) := ⟨by
      rw [Measure.restrict_apply_univ, torus]
      exact measure_Ioc_lt_top⟩
    let B : ℝ := 5 * (4 * (q.K * q.delta |p₁|)⁻¹ ^ 2)
    apply Integrable.of_bound henergyMeasurable.aestronglyMeasurable B
    filter_upwards with r
    have hweightNonneg : 0 ≤ q.lambda + dispersion p₁ + dispersion r :=
      add_nonneg (add_nonneg hq.1.le (dispersion_nonneg p₁)) (dispersion_nonneg r)
    have hweightLe : q.lambda + dispersion p₁ + dispersion r ≤ 5 := by
      linarith [dispersion_le_two p₁, dispersion_le_two r, hq.2.1]
    have hcoeff := degreeOneCoefficient_norm_sq_bound hq hsinpNe (r := r)
    rw [degreeOneEnergyIntegrand, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hweightNonneg (sq_nonneg _))]
    exact mul_le_mul hweightLe hcoeff (sq_nonneg _) (by norm_num)
  have hmixedMeasurable : Measurable (mixedResidualHMinusIntegrand q p₁) := by
    unfold mixedResidualHMinusIntegrand
    have hw : Measurable (fun z : ℝ × ℝ => mixedHMinusWeight q z.1 z.2) := by
      unfold mixedHMinusWeight dispersion
      fun_prop
    have hr : Measurable (fun z : ℝ × ℝ => mixedResidual q p₁ z.1) := by
      unfold mixedResidual
      exact (measurable_const.mul
        (Real.continuous_sin.measurable.comp measurable_fst).complex_ofReal).mul
          (degreeOneCoefficient_measurable.comp measurable_fst)
    exact hw.mul (hr.norm.pow_const 2)
  have hmixedIntegrable : Integrable (mixedResidualHMinusIntegrand q p₁)
      ((volume.restrict torus).prod (volume.restrict torus)) := by
    letI : IsFiniteMeasure (volume.restrict torus) := ⟨by
      rw [Measure.restrict_apply_univ, torus]
      exact measure_Ioc_lt_top⟩
    apply Integrable.of_bound hmixedMeasurable.aestronglyMeasurable q.lambda⁻¹
    filter_upwards with z
    have hdenPos : 0 < q.lambda + dispersion z.1 + dispersion z.2 :=
      add_pos_of_pos_of_nonneg
        (add_pos_of_pos_of_nonneg hq.1 (dispersion_nonneg z.1))
        (dispersion_nonneg z.2)
    have hweightNonneg : 0 ≤ mixedHMinusWeight q z.1 z.2 := by
      unfold mixedHMinusWeight
      exact inv_nonneg.mpr hdenPos.le
    have hweightLe : mixedHMinusWeight q z.1 z.2 ≤ q.lambda⁻¹ := by
      unfold mixedHMinusWeight
      apply (inv_le_inv₀ hdenPos hq.1).2
      linarith [dispersion_nonneg z.1, dispersion_nonneg z.2]
    have hresidual := mixedResidual_norm_sq_le_one hsinpNe hleft hright (r := z.1)
    rw [mixedResidualHMinusIntegrand, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hweightNonneg (sq_nonneg _))]
    simpa only [mul_one] using
      mul_le_mul hweightLe hresidual (sq_nonneg _) (inv_nonneg.mpr hq.1.le)
  have htwoMeasurable : Measurable (twoRowResidualHMinusIntegrand q p₁ p₂) := by
    unfold twoRowResidualHMinusIntegrand
    exact (twoRowWeight_measurable q p₁ p₂).mul
      (((measurable_const.mul measurable_const).mul
        (((degreeOneCoefficient_measurable.comp measurable_fst).add
          (degreeOneCoefficient_measurable.comp measurable_snd)))).norm.pow_const 2)
  have htwoIntegrable : Integrable (twoRowResidualHMinusIntegrand q p₁ p₂)
      ((volume.restrict torus).prod (volume.restrict torus)) := by
    simpa only [twoRowResidualHMinusIntegrand, twoRowOriginal, Function.uncurry_apply_pair]
      using twoRowOriginal_integrable hq (p₂ := p₂) hsinpNe
  refine ⟨henergyMeasurable, henergyIntegrable, hmixedMeasurable, hmixedIntegrable,
    htwoMeasurable, htwoIntegrable, ?_, ?_⟩
  · rw [mixedResidualHMinusSq]
    exact torusIntegral₂_eq_prodIntegral
      (fun r beta => mixedHMinusWeight q r beta * ‖mixedResidual q p₁ r‖ ^ 2)
      (by simpa only [mixedResidualHMinusIntegrand, Function.uncurry_apply_pair]
        using hmixedIntegrable)
  · rw [twoRowResidualHMinusSq]
    exact torusIntegral₂_eq_prodIntegral
      (fun r r' =>
        let alpha := r + r' - p₂
        twoRowHMinusWeight q p₁ alpha *
          ‖Complex.I * (Real.sin p₁ : ℂ) *
            (degreeOneCoefficient q p₁ r + degreeOneCoefficient q p₁ r')‖ ^ 2)
      (by simpa only [twoRowResidualHMinusIntegrand, Function.uncurry_apply_pair]
        using htwoIntegrable)

/-- Version-3 successor of Lemma 4.1. In addition to the printed
bounds, the statement exposes measurability, integrability, and finite
product-integral identities for all three energy integrands. -/
def LemmaFourTwoSuccessorV3Claim (K rho : ℝ) : Prop :=
  20 ≤ K → 0 < rho → rho ≤ Real.pi / 20 →
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ lambda : ℝ, 0 < lambda → lambda ≤ 1 →
    ∀ p₁ p₂ : ℝ, p₁ ∈ torus → p₂ ∈ torus → |p₂| ≤ |p₁| → 0 < |p₁| →
      let q : Parameters := ⟨lambda, K, rho⟩
      q.logThreshold < q.scaleLog |p₁| →
      LemmaFourTwoIntegralCertificate q p₁ p₂ ∧
      degreeZeroAdjoint p₁ (degreeOneCoefficient q p₁) =
          -(degreeOneNormalization q p₁ : ℂ) ∧
      c * |p₁| * q.scaleLog |p₁| ≤ degreeOneNormalization q p₁ ∧
      degreeOneEnergy q p₁ ≤ C ∧
      (∀ r : ℝ, mixedResidual q p₁ r = signedSupportIndicator q p₁ r) ∧
      c * q.scaleLog |p₁| ≤ mixedResidualHMinusSq q p₁ ∧
      mixedResidualHMinusSq q p₁ ≤ C * q.scaleLog |p₁| ∧
      twoRowResidualHMinusSq q p₁ p₂ (degreeOneCoefficient q p₁) ≤ C

/-- Provider for the version-3 Lemma 4.1 successor. -/
theorem lemmaFourTwoSuccessorV3Claim_proved (K rho : ℝ) :
    LemmaFourTwoSuccessorV3Claim K rho := by
  intro hK hrhoPos hrhoUpper
  obtain ⟨c, C, hc, hC, hold⟩ :=
    lemmaFourTwoSuccessorClaim_proved K rho hK hrhoPos hrhoUpper
  refine ⟨c, C, hc, hC, ?_⟩
  intro lambda hlambdaPos hlambdaUpper p₁ p₂ hp₁Torus hp₂Torus hpOrder hpPos
  let q : Parameters := ⟨lambda, K, rho⟩
  change q.logThreshold < q.scaleLog |p₁| → _
  intro hlog
  have hq : q.Admissible :=
    ⟨hlambdaPos, hlambdaUpper, hK, hrhoPos, hrhoUpper⟩
  obtain ⟨hsupport, _hscale, _hlogInterval⟩ :=
    oneCoin_regime hq (abs_nonneg p₁) hlog
  exact ⟨lemmaFourTwoIntegralCertificate_proved hq hpPos hsupport,
    hold lambda hlambdaPos hlambdaUpper p₁ p₂ hp₁Torus hp₂Torus hpOrder hpPos hlog⟩

end

end Manhattan.Estimates
