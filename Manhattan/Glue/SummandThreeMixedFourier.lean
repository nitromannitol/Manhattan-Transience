import Manhattan.Glue.SummandThreeMixed

/-!
# The mixed degree-two frequency function of summand 3

This module supplies the Fourier-side machinery that identifies the frequency
function of the mixed (type-`12`) degree-two sector of the residual
`D₁f_p - D₂*k_p`.  It is what
`Manhattan.Glue.type12FreqFun_eq_of_mFourierCoeff` consumes and what
`Manhattan.Glue.hMinusEnergy_type12WalshSynthesis_torusIntegral` needs in order
to turn the sector energy into the scalar integral bounded by
`Manhattan.Glue.mixedRawResidualHMinusSq_le_sqrtScale`.

Paper: `manuscript.tex:888-940`, `manuscript.tex:1138-1141`.
-/

open MeasureTheory Set

namespace Manhattan.Glue

noncomputable section

open Manhattan.Estimates

/-! ## The Fourier coordinates of a real-frequency representative -/

theorem fourierBasis_repr_realTorusL2_eq (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc (-Real.pi) Real.pi))) (k : ℤ) :
    fourierBasis.repr (Manhattan.realTorusL2 f hf) k =
      Estimates.torusIntegral fun x => intCharacter (-k) x * f x := by
  rw [fourierBasis_repr]
  have hcongr := congrFun (fourierCoeff_congr_ae
    (Manhattan.coeFn_realTorusL2 f hf)) k
  rw [hcongr, fourierCoeff_liftIoc_eq, fourierCoeffOn_eq_integral]
  have hend : -Real.pi + torusPeriod = Real.pi := by
    rw [Manhattan.torusPeriod]; ring
  rw [hend]
  simp only [smul_eq_mul]
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi),
    Estimates.torusIntegral, Estimates.torus,
    show Real.pi - -Real.pi = 2 * Real.pi by ring]
  simp only [one_div]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc (fun x _ => ?_)
  congr 1
  rw [fourier_coe_apply, intCharacter]
  congr 1
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp

/-- The `(shift)` phase on a general Fourier coordinate. -/
theorem fourierBasis_repr_rowTorusShift (s : ℝ)
    (F : Lp ℂ 2 (AddCircle.haarAddCircle : Measure (AddCircle Manhattan.torusPeriod)))
    (k : ℤ) :
    fourierBasis.repr (rowTorusShift s F) k =
      intCharacter k s * fourierBasis.repr F k := by
  have hstep : ∀ G : Lp ℂ 2
      (AddCircle.haarAddCircle : Measure (AddCircle Manhattan.torusPeriod)),
      fourierBasis.repr G k =
        ∫ t, (fourier (-k) t : ℂ) • (G : AddCircle Manhattan.torusPeriod → ℂ) t
          ∂(AddCircle.haarAddCircle) := by
    intro G
    rw [fourierBasis_repr]
    rfl
  rw [hstep, hstep]
  have hae : (fun t : AddCircle Manhattan.torusPeriod =>
        (fourier (-k) t : ℂ) •
          (rowTorusShift s F : AddCircle Manhattan.torusPeriod → ℂ) t)
      =ᵐ[(AddCircle.haarAddCircle : Measure (AddCircle Manhattan.torusPeriod))]
      fun t => (fourier (-k) t : ℂ) •
        (F : AddCircle Manhattan.torusPeriod → ℂ)
          (t + ((s : ℝ) : AddCircle Manhattan.torusPeriod)) := by
    filter_upwards [coeFn_rowTorusShift s F] with t ht
    rw [ht]
  rw [integral_congr_ae hae]
  have hfs : (fourier (-k) ((s : ℝ) : AddCircle Manhattan.torusPeriod) : ℂ) =
      intCharacter (-k) s := by
    rw [fourier_coe_apply, intCharacter, Manhattan.torusPeriod]
    congr 1
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    push_cast
    field_simp
  simp only [smul_eq_mul]
  have key : ∀ t : AddCircle Manhattan.torusPeriod,
      (fourier (-k) t : ℂ) *
          (F : AddCircle Manhattan.torusPeriod → ℂ)
            (t + ((s : ℝ) : AddCircle Manhattan.torusPeriod)) =
        intCharacter k s *
          ((fourier (-k) (t + ((s : ℝ) : AddCircle Manhattan.torusPeriod)) : ℂ) *
            (F : AddCircle Manhattan.torusPeriod → ℂ)
              (t + ((s : ℝ) : AddCircle Manhattan.torusPeriod))) := by
    intro t
    rw [fourier_add_arg, hfs]
    have hone : intCharacter k s * intCharacter (-k) s = 1 := by
      rw [intCharacter_add_index]
      simp [intCharacter]
    calc (fourier (-k) t : ℂ) *
        (F : AddCircle Manhattan.torusPeriod → ℂ)
          (t + ((s : ℝ) : AddCircle Manhattan.torusPeriod))
        = (intCharacter k s * intCharacter (-k) s) * ((fourier (-k) t : ℂ) *
            (F : AddCircle Manhattan.torusPeriod → ℂ)
              (t + ((s : ℝ) : AddCircle Manhattan.torusPeriod))) := by
          rw [hone, one_mul]
      _ = _ := by ring
  simp only [key]
  rw [integral_const_mul]
  congr 1
  exact integral_add_right_eq_self
    (fun t => (fourier (-k) t : ℂ) * (F : AddCircle Manhattan.torusPeriod → ℂ) t) _

/-! ## The two-dimensional angle torus -/

section TorusTwoComplex

attribute [local instance] Real.fact_zero_lt_one
attribute [local instance] cubicUnitAddCircleMeasureSpace

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The complex form of `Manhattan.Glue.integral_unitTorus_two`. -/
theorem integral_unitTorus_two_complex {F : ℝ → ℝ → ℂ} (hF : TorusBoundedTwo F) :
    (∫ x : UnitAddTorus (Fin 2),
        F (Manhattan.unitTorusAngle (x 0)) (Manhattan.unitTorusAngle (x 1)))
      = Estimates.torusIntegral fun r => Estimates.torusIntegral fun b => F r b := by
  obtain ⟨hm, C, hC⟩ := hF
  have hF' : TorusBoundedTwo F := ⟨hm, C, hC⟩
  have hout : TorusBoundedOne fun r => Estimates.torusIntegral fun b => F r b :=
    hF'.integral_right
  have h0 : Measurable fun x : UnitAddTorus (Fin 2) =>
      Manhattan.unitTorusAngle (x 0) :=
    Manhattan.unitTorusAngle_measurable.comp (measurable_pi_apply 0)
  have h1 : Measurable fun x : UnitAddTorus (Fin 2) =>
      Manhattan.unitTorusAngle (x 1) :=
    Manhattan.unitTorusAngle_measurable.comp (measurable_pi_apply 1)
  have hmeasT : Measurable fun x : UnitAddTorus (Fin 2) =>
      F (Manhattan.unitTorusAngle (x 0)) (Manhattan.unitTorusAngle (x 1)) :=
    hm.comp (h0.prodMk h1)
  have hint : Integrable fun x : UnitAddTorus (Fin 2) =>
      F (Manhattan.unitTorusAngle (x 0)) (Manhattan.unitTorusAngle (x 1)) :=
    Integrable.mono' (integrable_const C) hmeasT.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => hC _ _)
  have key : ∀ L : ℂ →L[ℝ] ℝ,
      (∫ x : UnitAddTorus (Fin 2),
          L (F (Manhattan.unitTorusAngle (x 0)) (Manhattan.unitTorusAngle (x 1)))) =
        L (Estimates.torusIntegral fun r => Estimates.torusIntegral fun b => F r b) := by
    intro L
    have hmeasL : Measurable fun z : ℝ × ℝ => L (F z.1 z.2) :=
      L.continuous.measurable.comp hm
    have hbL : ∀ r b : ℝ, |L (F r b)| ≤ ‖L‖ * C := by
      intro r b
      have hh1 : ‖L (F r b)‖ ≤ ‖L‖ * ‖F r b‖ := L.le_opNorm _
      have hh2 : ‖L‖ * ‖F r b‖ ≤ ‖L‖ * C :=
        mul_le_mul_of_nonneg_left (hC r b) (norm_nonneg L)
      simpa [Real.norm_eq_abs] using hh1.trans hh2
    rw [integral_unitTorus_two (fun r b => L (F r b)) hmeasL hbL]
    have step1 : ∀ r : ℝ,
        (Estimates.torusIntegral fun b => L (F r b)) =
          L (Estimates.torusIntegral fun b => F r b) :=
      fun r => map_torusIntegral L (hF'.integrable_right r)
    simp only [step1]
    exact map_torusIntegral L hout.integrable
  apply Complex.ext
  · simpa using (Complex.reCLM.integral_comp_comm hint).symm.trans (key Complex.reCLM)
  · simpa using (Complex.imCLM.integral_comp_comm hint).symm.trans (key Complex.imCLM)

/-- The angle-coordinate function attached to a bounded measurable symbol. -/
def mixedAngleFun (G : ℝ → ℝ → ℂ) (t : UnitAddTorus (Fin 2)) : ℂ :=
  G (Manhattan.unitTorusAngle (t 0)) (Manhattan.unitTorusAngle (t 1))

theorem mixedAngleFun_memLp {G : ℝ → ℝ → ℂ} (hG : TorusBoundedTwo G) :
    MemLp (mixedAngleFun G) 2 (LineTorusMeasure 2) := by
  obtain ⟨hm, C, hC⟩ := hG
  have h0 : Measurable fun t : UnitAddTorus (Fin 2) =>
      Manhattan.unitTorusAngle (t 0) :=
    Manhattan.unitTorusAngle_measurable.comp (measurable_pi_apply 0)
  have h1 : Measurable fun t : UnitAddTorus (Fin 2) =>
      Manhattan.unitTorusAngle (t 1) :=
    Manhattan.unitTorusAngle_measurable.comp (measurable_pi_apply 1)
  refine MemLp.of_bound ((hm.comp (h0.prodMk h1)).aestronglyMeasurable) C ?_
  filter_upwards with t
  exact hC _ _

/-- The `L²` vector of a bounded measurable mixed symbol. -/
def mixedAngleL2 {G : ℝ → ℝ → ℂ} (hG : TorusBoundedTwo G) :
    Lp ℂ 2 (LineTorusMeasure 2) :=
  (mixedAngleFun_memLp hG).toLp (mixedAngleFun G)

theorem coeFn_mixedAngleL2 {G : ℝ → ℝ → ℂ} (hG : TorusBoundedTwo G) :
    (mixedAngleL2 hG : UnitAddTorus (Fin 2) → ℂ)
      =ᵐ[LineTorusMeasure 2] mixedAngleFun G :=
  (mixedAngleFun_memLp hG).coeFn_toLp

/-- Multiplying by the two characters keeps a bounded mixed symbol bounded. -/
theorem torusBounded₂_character_mul {G : ℝ → ℝ → ℂ} (hG : TorusBoundedTwo G)
    (n : Fin 2 → ℤ) :
    TorusBoundedTwo fun r b =>
      intCharacter (-n 0) r * intCharacter (-n 1) b * G r b := by
  obtain ⟨hm, C, hC⟩ := hG
  refine ⟨?_, C, fun r b => ?_⟩
  · exact (((measurable_intCharacter (-n 0)).comp measurable_fst).mul
      ((measurable_intCharacter (-n 1)).comp measurable_snd)).mul hm
  · rw [norm_mul, norm_mul, norm_intCharacter, norm_intCharacter, one_mul, one_mul]
    exact hC r b

/-- **The two-dimensional Fourier bridge.**  The Fourier coefficients of a
bounded measurable mixed symbol, read on the abstract frequency torus, are the
iterated normalized torus integrals of the paper. -/
theorem mFourierCoeff_mixedAngleL2 {G : ℝ → ℝ → ℂ} (hG : TorusBoundedTwo G)
    (n : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff
        ((mixedAngleL2 hG : UnitAddTorus (Fin 2) → ℂ)) n =
      Estimates.torusIntegral fun r => Estimates.torusIntegral fun b =>
        intCharacter (-n 0) r * intCharacter (-n 1) b * G r b := by
  classical
  set F : ℝ → ℝ → ℂ := fun r b =>
    intCharacter (-n 0) r * intCharacter (-n 1) b * G r b with hFdef
  have hFB : TorusBoundedTwo F := torusBounded₂_character_mul hG n
  have hcoeff : UnitAddTorus.mFourierCoeff
      ((mixedAngleL2 hG : UnitAddTorus (Fin 2) → ℂ)) n
      = ∫ x : UnitAddTorus (Fin 2),
          F (Manhattan.unitTorusAngle (x 0)) (Manhattan.unitTorusAngle (x 1)) := by
    rw [UnitAddTorus.mFourierCoeff]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_mixedAngleL2 hG] with x hx
    rw [hx, smul_eq_mul, mFourier_eq_exp_angle, hFdef, mixedAngleFun]
    show _ = intCharacter (-n 0) _ * intCharacter (-n 1) _ * _
    congr 1
    rw [intCharacter, intCharacter, ← Complex.exp_add]
    congr 1
    rw [Fin.sum_univ_two]
    simp only [Pi.neg_apply]
    push_cast
    ring
  rw [hcoeff, integral_unitTorus_two_complex hFB]

end TorusTwoComplex

/-! ## Translating the normalized torus integral -/

/-- Translation invariance of the normalized torus integral for a function
supported in a window strictly inside the fundamental domain. -/
theorem torusIntegral_translate_window {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {h : ℝ → E} {c w : ℝ}
    (hwc : w + |c| < Real.pi)
    (hsupp : ∀ s, s ∉ Icc (-w) w → h s = 0) :
    (Estimates.torusIntegral fun r' => h (c + r')) = Estimates.torusIntegral h := by
  have hzero : ∀ d : ℝ, |d| ≤ |c| → ∀ r' : ℝ,
      r' ∉ Estimates.torus → h (d + r') = 0 := by
    intro d hd r' hr'
    have hdabs := abs_le.mp hd
    apply hsupp
    rw [Estimates.torus, mem_Ioc, not_and_or] at hr'
    intro hmem
    rw [mem_Icc] at hmem
    rcases hr' with hlow | hhigh
    · have hle : r' ≤ -Real.pi := le_of_not_gt hlow
      have : d + r' < -w := by linarith [hdabs.1, hdabs.2]
      linarith [hmem.1]
    · have hgt : Real.pi < r' := lt_of_not_ge hhigh
      have : w < d + r' := by linarith [hdabs.1, hdabs.2]
      linarith [hmem.2]
  unfold Estimates.torusIntegral
  congr 1
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun r' hr' => hzero c le_rfl r' hr'),
    setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun r' hr' => by simpa using hzero 0 (by simp [abs_nonneg]) r' hr')]
  exact integral_add_left_eq_self h c

/-- Translation invariance of the normalized torus integral for a
`2π`-periodic function. -/
theorem torusIntegral_translate_periodic {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {h : ℝ → E} (hper : Function.Periodic h (2 * Real.pi))
    (c : ℝ) :
    (Estimates.torusIntegral fun r' => h (c + r')) = Estimates.torusIntegral h := by
  have hle : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  unfold Estimates.torusIntegral Estimates.torus
  congr 1
  rw [← intervalIntegral.integral_of_le hle, ← intervalIntegral.integral_of_le hle]
  rw [intervalIntegral.integral_comp_add_left (fun x => h x) c]
  have h1 : c + -Real.pi + 2 * Real.pi = c + Real.pi := by ring
  have h2 : -Real.pi + 2 * Real.pi = Real.pi := by ring
  calc (∫ x in (c + -Real.pi)..(c + Real.pi), h x)
      = ∫ x in (c + -Real.pi)..(c + -Real.pi + 2 * Real.pi), h x := by rw [h1]
    _ = ∫ x in (-Real.pi)..(-Real.pi + 2 * Real.pi), h x :=
        hper.intervalIntegral_add_eq _ _
    _ = ∫ x in (-Real.pi)..Real.pi, h x := by rw [h2]

/-! ## The support of the explicit correction -/

theorem correctionV_eq_zero_of_notMem {kappa : ℝ} {q : Parameters} {a r beta : ℝ}
    (hr : r ∉ q.supportInterval a) : correctionV kappa q a r beta = 0 := by
  simp [correctionV, hr]

theorem delta_nonneg {q : Parameters} {a : ℝ} (ha : 0 ≤ a) : 0 ≤ q.delta a := by
  rw [Parameters.delta]
  positivity

theorem nonneg_of_mem_supportInterval {q : Parameters} (hq : q.Admissible) {a r : ℝ}
    (ha : 0 ≤ a) (hr : r ∈ q.supportInterval a) : 0 ≤ r := by
  have hK : (0 : ℝ) < q.K := by linarith [hq.2.2.1]
  have := hr.1
  nlinarith [delta_nonneg (q := q) ha]

theorem r0_le_two_rho {q : Parameters} (hq : q.Admissible) : q.r0 ≤ 2 * q.rho := by
  have hK : (20 : ℝ) ≤ q.K := hq.2.2.1
  have hrho : 0 < q.rho := hq.2.2.2.1
  rw [Parameters.r0]
  rw [div_le_iff₀ (by nlinarith)]
  nlinarith

theorem two_r0_le_rho {q : Parameters} (hq : q.Admissible) : 2 * q.r0 ≤ q.rho := by
  have hK : (20 : ℝ) ≤ q.K := hq.2.2.1
  have hrho : 0 < q.rho := hq.2.2.2.1
  rw [Parameters.r0]
  rw [show 2 * (q.rho / (100 * q.K)) = (2 * q.rho) / (100 * q.K) by ring,
    div_le_iff₀ (by nlinarith)]
  nlinarith

/-- Outside a small band of column frequencies the correction interval is
empty. -/
theorem correctionInterval_eq_empty_of_beta {q : Parameters} (hq : q.Admissible)
    {a x beta : ℝ} (ha : 0 ≤ a) (hbeta : q.rho / (8 * q.K) < |beta|) :
    correctionInterval q a x beta = ∅ := by
  rw [correctionInterval]
  rw [if_neg]
  rintro ⟨hx, hle⟩
  have hx0 : 0 ≤ x := nonneg_of_mem_supportInterval hq ha hx
  have hd : 0 ≤ q.delta a := delta_nonneg (q := q) ha
  linarith

/-- The correction vanishes off a small band of column frequencies. -/
theorem correctionCoefficient_eq_zero_of_beta {q : Parameters} (hq : q.Admissible)
    {a p₂ r r' beta : ℝ} (ha : 0 ≤ a) (hbeta : q.rho / (8 * q.K) < |beta|) :
    correctionCoefficient 40 q a p₂ r r' beta = 0 := by
  simp only [correctionCoefficient,
    correctionInterval_eq_empty_of_beta hq ha hbeta, Set.mem_empty_iff_false,
    if_false, mul_zero, add_zero]

/-- The correction vanishes off a small band of row frequencies. -/
theorem correctionCoefficient_eq_zero_of_row {q : Parameters} (hq : q.Admissible)
    {a p₂ r r' beta : ℝ} (ha : 0 ≤ a) (hp₂ : |p₂| ≤ a)
    (hr : r ∉ Icc (-(2 * q.rho)) (2 * q.rho)) :
    correctionCoefficient 40 q a p₂ r r' beta = 0 := by
  classical
  have hK : (20 : ℝ) ≤ q.K := hq.2.2.1
  have hKpos : (0 : ℝ) < q.K := by linarith
  have hrho : 0 < q.rho := hq.2.2.2.1
  have hd : 0 ≤ q.delta a := delta_nonneg (q := q) ha
  have hr0 := r0_le_two_rho hq
  have h2r0 := two_r0_le_rho hq
  have hp₂abs := abs_le.mp hp₂
  have hade : a ≤ q.delta a := by
    rw [Parameters.delta]
    linarith [Real.sqrt_nonneg q.lambda]
  have hfirst : correctionV 40 q a r beta = 0 := by
    refine correctionV_eq_zero_of_notMem ?_
    intro hmem
    exact hr ⟨by linarith [nonneg_of_mem_supportInterval hq ha hmem],
      le_trans hmem.2 hr0⟩
  have hkey : correctionV 40 q a r' beta = 0 ∨
      r + r' - p₂ ∉ correctionInterval q a r' beta := by
    by_cases hmem : r' ∈ q.supportInterval a
    · right
      intro hin
      by_cases hcond : r' ∈ q.supportInterval a ∧
          r' + q.delta a + |beta| ≤ q.rho / (8 * q.K)
      · rw [correctionInterval, if_pos hcond, mem_Icc] at hin
        have hr'0 : 0 ≤ r' := nonneg_of_mem_supportInterval hq ha hmem
        have hr'le : r' ≤ q.r0 := hmem.2
        have hKd : q.K * q.delta a ≤ r' := hmem.1
        have hdle : q.delta a ≤ q.r0 := by nlinarith
        have hale : a ≤ q.r0 := le_trans hade hdle
        have hupper : -4 * q.K * (r' + q.delta a + |beta|) ≤ 0 := by
          have hnn : 0 ≤ r' + q.delta a + |beta| := by positivity
          nlinarith
        exact hr ⟨by linarith [hin.1], by linarith [hin.2]⟩
      · rw [correctionInterval, if_neg hcond] at hin
        exact hin
    · exact Or.inl (correctionV_eq_zero_of_notMem hmem)
  rcases hkey with h | h <;>
    simp [correctionCoefficient, hfirst, h]


theorem rawD2StarMixed_eq_zero_of_forall {k : ℝ → ℝ → ℝ → ℂ} {r beta : ℝ}
    (h : ∀ r', k r r' beta = 0) : rawD2StarMixed k r beta = 0 := by
  rw [rawD2StarMixed]
  have hz : (Estimates.torusIntegral fun r' => k r r' beta) = 0 := by
    have : (fun r' => k r r' beta) = fun _ : ℝ => (0 : ℂ) := funext h
    rw [this, torusIntegral_const]
  rw [hz, mul_zero]

theorem rawD2StarMixed_correction_eq_zero_of_row {q : Parameters} (hq : q.Admissible)
    {a p₂ r beta : ℝ} (ha : 0 ≤ a) (hp₂ : |p₂| ≤ a)
    (hr : r ∉ Icc (-(2 * q.rho)) (2 * q.rho)) :
    rawD2StarMixed (correctionCoefficient 40 q a p₂) r beta = 0 :=
  rawD2StarMixed_eq_zero_of_forall
    (fun _ => correctionCoefficient_eq_zero_of_row hq ha hp₂ hr)

theorem rawD2StarMixed_correction_eq_zero_of_beta {q : Parameters} (hq : q.Admissible)
    {a p₂ r beta : ℝ} (ha : 0 ≤ a) (hbeta : q.rho / (8 * q.K) < |beta|) :
    rawD2StarMixed (correctionCoefficient 40 q a p₂) r beta = 0 :=
  rawD2StarMixed_eq_zero_of_forall
    (fun _ => correctionCoefficient_eq_zero_of_beta hq ha hbeta)

theorem rawMixedTarget_eq_zero_of_row {q : Parameters} (hq : q.Admissible)
    {a r : ℝ} (ha : 0 ≤ a) (hr : r ∉ Icc (-(2 * q.rho)) (2 * q.rho)) :
    rawMixedTarget q a r = 0 := by
  classical
  rw [rawMixedTarget, if_neg]
  intro hmem
  exact hr ⟨by
      linarith [nonneg_of_mem_supportInterval hq ha hmem, hq.2.2.2.1],
    le_trans hmem.2 (r0_le_two_rho hq)⟩

theorem mixedRawResidual_eq_zero_of_row {q : Parameters} (hq : q.Admissible)
    {a p₂ r beta : ℝ} (ha : 0 ≤ a) (hp₂ : |p₂| ≤ a)
    (hr : r ∉ Icc (-(2 * q.rho)) (2 * q.rho)) :
    mixedRawResidual q a p₂ r beta = 0 := by
  rw [mixedRawResidual, rawMixedTarget_eq_zero_of_row hq ha hr,
    rawD2StarMixed_correction_eq_zero_of_row hq ha hp₂ hr]
  simp

/-! ## The coincident-row mode dropped by the concrete lowering -/

theorem rawD2StarMixed_periodizeRow (k : ℝ → ℝ → ℝ → ℂ) (r beta : ℝ) :
    rawD2StarMixed (periodizeRow k) r beta = rawD2StarMixed k r beta := by
  rw [rawD2StarMixed, rawD2StarMixed]
  congr 1
  refine torusIntegral_congr_on_torus ?_
  intro r' hr'
  exact periodizeRow_eq hr' r beta

/-- **The projected mixed lowering symbol.**  It differs from the raw one by
the coincident-row mode of Lemma 5.3, which does not depend on the row
frequency. -/
theorem rawD2StarMixed_rawOffDiagonalPart_eq {k : ℝ → ℝ → ℝ → ℂ}
    (hk : TorusBoundedThree k)
    (hper : ∀ r beta : ℝ, Function.Periodic (fun r' => k r r' beta) (2 * Real.pi))
    (p₂ r beta : ℝ) :
    rawD2StarMixed (rawOffDiagonalPart p₂ k) r beta =
      rawD2StarMixed k r beta -
        projectionMixedError (rawDiagonalPart p₂ k) beta := by
  have hoff : TorusBoundedThree (rawOffDiagonalPart p₂ k) :=
    torusBounded₃_rawOffDiagonalPart hk p₂
  have hsplit : (fun a b c => k a b c - rawOffDiagonalPart p₂ k a b c) =
      diagonalRawCarrier p₂ (rawDiagonalPart p₂ k) := by
    funext a b c
    exact sub_rawOffDiagonalPart p₂ k a b c
  have h := rawD2StarMixed_sub hk hoff r beta
  rw [hsplit, rawD2StarMixed_diagonalRawCarrier p₂ _
    (rawDiagonalPart_periodic p₂ hper) r beta] at h
  rw [h]
  ring

theorem TorusBoundedThree.rawD2StarMixed {k : ℝ → ℝ → ℝ → ℂ}
    (hk : TorusBoundedThree k) :
    TorusBoundedTwo (Manhattan.Glue.rawD2StarMixed k) := by
  obtain ⟨hm, C, hC⟩ := hk
  have hCnonneg : 0 ≤ C := le_trans (norm_nonneg _) (hC 0 0 0)
  constructor
  · have hcomp : Measurable fun w : (ℝ × ℝ) × ℝ => k w.1.1 w.2 w.1.2 :=
      hm.comp ((measurable_fst.comp measurable_fst).prodMk
        (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))
    have hint : Measurable fun z : ℝ × ℝ =>
        Estimates.torusIntegral fun r' => k z.1 r' z.2 :=
      (stronglyMeasurable_torusIntegral hcomp.stronglyMeasurable).measurable
    have hsin : Measurable fun z : ℝ × ℝ =>
        (-Complex.I * (Real.sin z.2 : ℂ)) := by fun_prop
    exact hsin.mul hint
  · refine ⟨C, fun r beta => ?_⟩
    rw [Manhattan.Glue.rawD2StarMixed, norm_mul, norm_mul, norm_neg,
      Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      |Real.sin beta| * ‖Estimates.torusIntegral fun r' => k r r' beta‖ ≤ 1 * C := by
        apply mul_le_mul (Real.abs_sin_le_one _)
          (norm_torusIntegral_le_of_bound (fun r' => hC r r' beta))
          (norm_nonneg _) zero_le_one
      _ = C := one_mul C

/-! ## Translating a mixed Fourier coefficient -/

/-- The `(shift)` phase splits off a character. -/
theorem intCharacter_shift (m : ℤ) (c s : ℝ) :
    intCharacter (-m) s = intCharacter m c * intCharacter (-m) (c + s) := by
  rw [intCharacter_add_arg, ← mul_assoc, intCharacter_add_index]
  simp

/-- **The `(s,u) → (r,β)` translation of a mixed Fourier coefficient**, given
the outer (row) translation. -/
theorem mixedFourierCoefficient_translate_of_outer {H : ℝ → ℝ → ℂ}
    {wb c1 c2 : ℝ} (h2 : wb + |c2| < Real.pi)
    (hb : ∀ r beta, beta ∉ Icc (-wb) wb → H r beta = 0) (m n : ℤ)
    (houter : (Estimates.torusIntegral fun s =>
          Estimates.torusIntegral fun beta =>
            intCharacter (-m) (c1 + s) * intCharacter (-n) beta * H (c1 + s) beta) =
        Estimates.torusIntegral fun r => Estimates.torusIntegral fun beta =>
          intCharacter (-m) r * intCharacter (-n) beta * H r beta) :
    (Estimates.torusIntegral fun s => Estimates.torusIntegral fun u =>
        intCharacter (-m) s * intCharacter (-n) u * H (c1 + s) (c2 + u)) =
      intCharacter m c1 * intCharacter n c2 * mixedFourierCoefficient H m n := by
  have hinner : ∀ s : ℝ,
      (Estimates.torusIntegral fun u =>
        intCharacter (-m) s * intCharacter (-n) u * H (c1 + s) (c2 + u)) =
      intCharacter m c1 * intCharacter n c2 *
        Estimates.torusIntegral fun beta =>
          intCharacter (-m) (c1 + s) * intCharacter (-n) beta * H (c1 + s) beta := by
    intro s
    have hstep : ∀ u : ℝ,
        intCharacter (-m) s * intCharacter (-n) u * H (c1 + s) (c2 + u) =
          intCharacter m c1 * intCharacter n c2 *
            (intCharacter (-m) (c1 + s) * intCharacter (-n) (c2 + u) *
              H (c1 + s) (c2 + u)) := by
      intro u
      rw [intCharacter_shift m c1 s, intCharacter_shift n c2 u]
      ring
    simp only [hstep]
    rw [torusIntegral_const_mul]
    congr 1
    refine torusIntegral_translate_window (E := ℂ)
      (h := fun beta => intCharacter (-m) (c1 + s) * intCharacter (-n) beta *
        H (c1 + s) beta) (c := c2) (w := wb) h2 ?_
    intro beta hbeta
    show intCharacter (-m) (c1 + s) * intCharacter (-n) beta * H (c1 + s) beta = 0
    rw [hb (c1 + s) beta hbeta, mul_zero]
  simp only [hinner]
  rw [torusIntegral_const_mul, houter, mixedFourierCoefficient]

theorem torusBounded₂_charMul₂ {A : ℝ → ℝ → ℂ} (hA : TorusBoundedTwo A) (n : ℤ) :
    TorusBoundedTwo fun r beta => intCharacter (-n) beta * A r beta := by
  obtain ⟨hm, C, hC⟩ := hA
  refine ⟨((measurable_intCharacter (-n)).comp measurable_snd).mul hm, C,
    fun r beta => ?_⟩
  rw [norm_mul, norm_intCharacter, one_mul]
  exact hC r beta

/-- The outer (row) translation for a mixed symbol which is a row-supported
part minus a row-independent part. -/
theorem TorusBoundedOne.shift {f : ℝ → ℂ} (hf : TorusBoundedOne f) (c : ℝ) :
    TorusBoundedOne fun x => f (c + x) := by
  obtain ⟨hm, C, hC⟩ := hf
  exact ⟨hm.comp (measurable_const.add measurable_id), C, fun x => hC (c + x)⟩

/-- The outer (row) translation for a mixed symbol which is a row-supported
part minus a row-independent part. -/
theorem torusIntegral_translate_row_sub_const {A : ℝ → ℝ → ℂ}
    (hA : TorusBoundedTwo A) {D : ℝ → ℂ} (hD : TorusBoundedOne D)
    {w c : ℝ} (hw : w + |c| < Real.pi)
    (hsupp : ∀ r beta, r ∉ Icc (-w) w → A r beta = 0) (m n : ℤ) :
    (Estimates.torusIntegral fun s => Estimates.torusIntegral fun beta =>
        intCharacter (-m) (c + s) * intCharacter (-n) beta *
          (A (c + s) beta - D beta)) =
      Estimates.torusIntegral fun r => Estimates.torusIntegral fun beta =>
        intCharacter (-m) r * intCharacter (-n) beta * (A r beta - D beta) := by
  set K : ℂ := Estimates.torusIntegral fun beta => intCharacter (-n) beta * D beta
    with hK
  have hAchar : TorusBoundedTwo fun r beta => intCharacter (-n) beta * A r beta :=
    torusBounded₂_charMul₂ hA n
  have hDchar : TorusBoundedOne fun beta => intCharacter (-n) beta * D beta :=
    TorusBoundedOne.charMul hD (-n)
  set P0 : ℝ → ℂ := fun r => intCharacter (-m) r *
    Estimates.torusIntegral (fun beta => intCharacter (-n) beta * A r beta) with hP0
  set P1 : ℝ → ℂ := fun r => intCharacter (-m) r * K with hP1
  have hP0B : TorusBoundedOne P0 := TorusBoundedOne.charMul hAchar.integral_right (-m)
  have hP1B : TorusBoundedOne P1 := by
    refine ⟨(measurable_intCharacter (-m)).mul measurable_const, ‖K‖, fun r => ?_⟩
    show ‖intCharacter (-m) r * K‖ ≤ ‖K‖
    rw [norm_mul, norm_intCharacter, one_mul]
  have hsplit : ∀ r : ℝ,
      (Estimates.torusIntegral fun beta =>
        intCharacter (-m) r * intCharacter (-n) beta * (A r beta - D beta)) =
      P0 r - P1 r := by
    intro r
    have hpt : ∀ beta : ℝ,
        intCharacter (-m) r * intCharacter (-n) beta * (A r beta - D beta) =
          intCharacter (-m) r * (intCharacter (-n) beta * A r beta) -
            intCharacter (-m) r * (intCharacter (-n) beta * D beta) := by
      intro beta; ring
    simp only [hpt]
    rw [torusIntegral_sub
      ((hAchar.integrable_right r).const_mul (intCharacter (-m) r))
      (hDchar.integrable.const_mul (intCharacter (-m) r)),
      torusIntegral_const_mul, torusIntegral_const_mul]
  have hshift : (Estimates.torusIntegral fun s =>
      (Estimates.torusIntegral fun beta =>
        intCharacter (-m) (c + s) * intCharacter (-n) beta *
          (A (c + s) beta - D beta))) =
      Estimates.torusIntegral fun s => P0 (c + s) - P1 (c + s) := by
    refine congrArg _ ?_
    funext s
    exact hsplit (c + s)
  rw [hshift]
  simp only [hsplit]
  rw [torusIntegral_sub (hP0B.shift c).integrable (hP1B.shift c).integrable,
    torusIntegral_sub hP0B.integrable hP1B.integrable]
  congr 1
  · refine torusIntegral_translate_window (E := ℂ) (h := P0) (c := c) (w := w) hw ?_
    intro r hr
    show intCharacter (-m) r *
      Estimates.torusIntegral (fun beta => intCharacter (-n) beta * A r beta) = 0
    have hz : (fun beta => intCharacter (-n) beta * A r beta) = fun _ : ℝ => (0 : ℂ) := by
      funext beta
      rw [hsupp r beta hr, mul_zero]
    rw [hz, torusIntegral_const, mul_zero]
  · refine torusIntegral_translate_periodic (E := ℂ) (h := P1) ?_ c
    intro r
    show intCharacter (-m) (r + 2 * Real.pi) * K = intCharacter (-m) r * K
    rw [intCharacter_periodic]

/-! ## The raising half of the mixed sector -/

theorem degreeOneCoefficient_eq_zero_of_row {q : Parameters} (hq : q.Admissible)
    {p₁ r : ℝ} (hr : r ∉ Icc (-(2 * q.rho)) (2 * q.rho)) :
    degreeOneCoefficient q p₁ r = 0 := by
  classical
  rw [degreeOneCoefficient, if_neg]
  intro hmem
  exact hr ⟨by
      linarith [nonneg_of_mem_supportInterval hq (abs_nonneg p₁) hmem, hq.2.2.2.1],
    le_trans hmem.2 (r0_le_two_rho hq)⟩

theorem intCharacter_one_eq (x : ℝ) :
    intCharacter 1 x = Complex.exp (Complex.I * (x : ℂ)) := by
  rw [intCharacter]
  norm_num

theorem intCharacter_neg_one_eq (x : ℝ) :
    intCharacter (-1) x = Complex.exp (-Complex.I * (x : ℂ)) := by
  rw [intCharacter]
  congr 1
  push_cast
  ring

/-- **The row Fourier coefficient of the mixed component of `D₁f_p`.** -/
theorem mixedResidual_rowFourier {q : Parameters} (hq : q.Admissible)
    {p : Fin 2 → ℝ} (hwin : 2 * q.rho + |p 1| < Real.pi)
    (hf : MemLp (degreeOneCoefficient q (p 0)) 2
      (volume.restrict (Ioc (-Real.pi) Real.pi))) (m : ℤ) :
    (Estimates.torusIntegral fun s =>
        intCharacter (-m) s * mixedResidual q (p 0) (p 1 + s)) =
      (2 : ℂ)⁻¹ *
        (Complex.exp (Complex.I * (p 1 : ℂ)) *
            fourierBasis.repr (rowTorusShift (p 1)
              (Manhattan.realTorusL2 (degreeOneCoefficient q (p 0)) hf)) (m - 1) -
          Complex.exp (-Complex.I * (p 1 : ℂ)) *
            fourierBasis.repr (rowTorusShift (p 1)
              (Manhattan.realTorusL2 (degreeOneCoefficient q (p 0)) hf)) (m + 1)) := by
  classical
  have hgint : Integrable (degreeOneCoefficient q (p 0))
      (volume.restrict Estimates.torus) := by
    rw [Estimates.torus]
    exact hf.integrable (by norm_num)
  have hchint : ∀ k : ℤ, Integrable
      (fun r => intCharacter (-k) r * degreeOneCoefficient q (p 0) r)
      (volume.restrict Estimates.torus) :=
    fun k => hgint.bdd_mul (c := 1)
      (measurable_intCharacter (-k)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => le_of_eq (norm_intCharacter _ _))
  have hzero : ∀ r : ℝ, r ∉ Icc (-(2 * q.rho)) (2 * q.rho) →
      intCharacter (-m) r * mixedResidual q (p 0) r = 0 := by
    intro r hr
    rw [mixedResidual, degreeOneCoefficient_eq_zero_of_row hq hr]
    ring
  have hshift : ∀ s : ℝ,
      intCharacter (-m) s * mixedResidual q (p 0) (p 1 + s) =
        intCharacter m (p 1) *
          (intCharacter (-m) (p 1 + s) * mixedResidual q (p 0) (p 1 + s)) := by
    intro s
    rw [intCharacter_shift m (p 1) s]
    ring
  simp only [hshift]
  rw [torusIntegral_const_mul]
  rw [torusIntegral_translate_window (E := ℂ)
    (h := fun r => intCharacter (-m) r * mixedResidual q (p 0) r)
    (c := p 1) (w := 2 * q.rho) hwin hzero]
  have hsplit : ∀ r : ℝ, intCharacter (-m) r * mixedResidual q (p 0) r =
      (2 : ℂ)⁻¹ * (intCharacter (-(m - 1)) r * degreeOneCoefficient q (p 0) r) -
        (2 : ℂ)⁻¹ * (intCharacter (-(m + 1)) r * degreeOneCoefficient q (p 0) r) := by
    intro r
    rw [mixedResidual]
    linear_combination (-(degreeOneCoefficient q (p 0) r)) * intCharacter_mul_neg_I_sin m r
  simp only [hsplit]
  rw [torusIntegral_sub ((hchint (m - 1)).const_mul _) ((hchint (m + 1)).const_mul _),
    torusIntegral_const_mul, torusIntegral_const_mul,
    fourierBasis_repr_rowTorusShift, fourierBasis_repr_rowTorusShift,
    fourierBasis_repr_realTorusL2_eq, fourierBasis_repr_realTorusL2_eq,
    ← intCharacter_one_eq, ← intCharacter_neg_one_eq]
  set X : ℂ := Estimates.torusIntegral fun x =>
    intCharacter (-(m - 1)) x * degreeOneCoefficient q (p 0) x with hX
  set Y : ℂ := Estimates.torusIntegral fun x =>
    intCharacter (-(m + 1)) x * degreeOneCoefficient q (p 0) x with hY
  have e1 : intCharacter 1 (p 1) * intCharacter (m - 1) (p 1) = intCharacter m (p 1) := by
    rw [intCharacter_add_index]
    congr 1
    ring
  have e2 : intCharacter (-1) (p 1) * intCharacter (m + 1) (p 1) = intCharacter m (p 1) := by
    rw [intCharacter_add_index]
    congr 1
    ring
  linear_combination (-(2 : ℂ)⁻¹ * X) * e1 + ((2 : ℂ)⁻¹ * Y) * e2

/-- **The raising half of the mixed sector coefficient.**  The `(m,n)` Fourier
coefficient of the mixed component of `D₁f_p`, read in the shifted frequency
variables of (shift). -/
theorem raisingHalf_fourierCoeff {q : Parameters} (hq : q.Admissible)
    {p : Fin 2 → ℝ} (hwin : 2 * q.rho + |p 1| < Real.pi)
    (hf : MemLp (degreeOneCoefficient q (p 0)) 2
      (volume.restrict (Ioc (-Real.pi) Real.pi))) (m n : ℤ) :
    (Estimates.torusIntegral fun s => Estimates.torusIntegral fun u =>
        intCharacter (-m) s * intCharacter (-n) u *
          ((Real.sign (Real.sin (p 0)) : ℂ) *
            ((rawMixedTarget q |p 0| (p 1 + s) : ℝ) : ℂ))) =
      (if n = 0 then
        (2 : ℂ)⁻¹ *
          (Complex.exp (Complex.I * (p 1 : ℂ)) *
              fourierBasis.repr (rowTorusShift (p 1)
                (Manhattan.realTorusL2 (degreeOneCoefficient q (p 0)) hf)) (m - 1) -
            Complex.exp (-Complex.I * (p 1 : ℂ)) *
              fourierBasis.repr (rowTorusShift (p 1)
                (Manhattan.realTorusL2 (degreeOneCoefficient q (p 0)) hf)) (m + 1))
      else 0) := by
  classical
  have hleft : 0 < q.K * q.delta |p 0| := by
    have hd : 0 < q.delta |p 0| := by
      rw [Parameters.delta]
      have := Real.sqrt_pos.mpr hq.1
      have := abs_nonneg (p 0)
      linarith
    have : (0 : ℝ) < q.K := by linarith [hq.2.2.1]
    positivity
  have hright : q.r0 < Real.pi := by
    have := r0_le_two_rho hq
    have hrho : q.rho ≤ Real.pi / 20 := hq.2.2.2.2
    linarith [Real.pi_pos]
  have hres : ∀ r : ℝ, (Real.sign (Real.sin (p 0)) : ℂ) *
      ((rawMixedTarget q |p 0| r : ℝ) : ℂ) = mixedResidual q (p 0) r := by
    intro r
    rw [mixedResidual_eq_sign_mul_rawMixedTarget hleft hright]
  simp only [hres]
  -- inner integral in `u`
  have hinner : ∀ s : ℝ,
      (Estimates.torusIntegral fun u =>
        intCharacter (-m) s * intCharacter (-n) u * mixedResidual q (p 0) (p 1 + s)) =
      (intCharacter (-m) s * mixedResidual q (p 0) (p 1 + s)) *
        (if n = 0 then (1 : ℂ) else 0) := by
    intro s
    have hpt : ∀ u : ℝ,
        intCharacter (-m) s * intCharacter (-n) u * mixedResidual q (p 0) (p 1 + s) =
          (intCharacter (-m) s * mixedResidual q (p 0) (p 1 + s)) *
            intCharacter (-n) u := by
      intro u; ring
    simp only [hpt]
    rw [torusIntegral_const_mul]
    congr 1
    rw [torusIntegral_intCharacter']
    simp
  simp only [hinner]
  rw [torusIntegral_mul_const, mixedResidual_rowFourier hq hwin hf m]
  by_cases hn : n = 0 <;> simp [hn]

/-! ## The lowering half of the mixed sector -/

theorem torusBounded₁_projectionMixedError {ell : ℝ → ℝ → ℂ}
    (hell : TorusBoundedTwo ell) : TorusBoundedOne (projectionMixedError ell) := by
  obtain ⟨hm, C, hC⟩ := hell
  have hCnonneg : 0 ≤ C := le_trans (norm_nonneg _) (hC 0 0)
  refine ⟨?_, C, fun beta => ?_⟩
  · have h : Measurable fun beta : ℝ =>
        Estimates.torusIntegral fun alpha : ℝ => ell alpha beta := by
      refine (stronglyMeasurable_torusIntegral (F := fun w : ℝ × ℝ => ell w.2 w.1)
        ?_).measurable
      exact (hm.comp (measurable_snd.prodMk measurable_fst)).stronglyMeasurable
    have hsin : Measurable fun beta : ℝ =>
        (-Complex.I * (Real.sin beta : ℂ)) := by fun_prop
    exact hsin.mul h
  · rw [projectionMixedError, norm_mul, norm_mul, norm_neg, Complex.norm_I,
      one_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      |Real.sin beta| *
          ‖Estimates.torusIntegral fun alpha : ℝ => ell alpha beta‖ ≤ 1 * C :=
        mul_le_mul (Real.abs_sin_le_one _)
          (norm_torusIntegral_le_of_bound (fun alpha => hC alpha beta))
          (norm_nonneg _) zero_le_one
      _ = C := one_mul C

/-- The coincident-row mode of the explicit correction is supported in a small
band of column frequencies. -/
theorem projectionMixedError_correction_eq_zero_of_beta {q : Parameters}
    (hq : q.Admissible) {a p₂ beta : ℝ} (ha : 0 ≤ a)
    (hbeta : q.rho / (8 * q.K) < |beta|) :
    projectionMixedError
        (rawDiagonalPart p₂ (periodizeRow (correctionCoefficient 40 q a p₂)))
        beta = 0 := by
  rw [projectionMixedError]
  have hz : (fun alpha : ℝ =>
      rawDiagonalPart p₂ (periodizeRow (correctionCoefficient 40 q a p₂)) alpha beta)
      = fun _ : ℝ => (0 : ℂ) := by
    funext alpha
    rw [rawDiagonalPart]
    have : (fun t : ℝ => periodizeRow (correctionCoefficient 40 q a p₂) t
        (alpha - t + p₂) beta) = fun _ : ℝ => (0 : ℂ) := by
      funext t
      rw [periodizeRow]
      exact correctionCoefficient_eq_zero_of_beta hq ha hbeta
    rw [this, torusIntegral_const]
  rw [hz, torusIntegral_const, mul_zero]

theorem rho_div_le_rho {q : Parameters} (hq : q.Admissible) :
    q.rho / (8 * q.K) ≤ q.rho := by
  have hK : (20 : ℝ) ≤ q.K := hq.2.2.1
  have hrho : 0 < q.rho := hq.2.2.2.1
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- **The lowering half of the mixed sector coefficient.**  The `(m,n)`
Fourier coefficient of the raw projected lowering symbol, read in the shifted
frequency variables of (shift), is the genuine mixed Walsh coefficient of
`D₂*` on the competitor's degree-three coefficient. -/
theorem loweringHalf_fourierCoeff {q : Parameters} (hq : q.Admissible)
    {p : Fin 2 → ℝ} (hp₂ : |p 1| ≤ |p 0|)
    (hwin1 : 2 * q.rho + |p 1| < Real.pi) (hwin2 : q.rho + |p 0| < Real.pi)
    (m n : ℤ) :
    (Estimates.torusIntegral fun s => Estimates.torusIntegral fun u =>
        intCharacter (-m) s * intCharacter (-n) u *
          rawD2StarMixed (rawOffDiagonalPart (p 1)
            (periodizeRow (correctionCoefficient 40 q |p 0| (p 1))))
            (p 1 + s) (p 0 + u)) =
      Manhattan.type112DStarMixed p
        (Manhattan.shiftedCorrectionType112Coefficients (kappa := 40)
          (by norm_num) hq.1 |p 0| (p 0) (p 1))
        ⟨mixedPairFinset (m, n), isType12Index_mixedPairFinset m n⟩ := by
  classical
  set a : ℝ := |p 0| with ha0
  have ha : 0 ≤ a := abs_nonneg _
  set k : ℝ → ℝ → ℝ → ℂ := correctionCoefficient 40 q a (p 1) with hk
  have hkB : TorusBoundedThree k :=
    torusBounded₃_correctionCoefficient (by norm_num) hq.1 a (p 1)
  have hpkB : TorusBoundedThree (periodizeRow k) := torusBounded₃_periodizeRow hkB
  have hper : ∀ r beta : ℝ,
      Function.Periodic (fun r' => periodizeRow k r r' beta) (2 * Real.pi) :=
    fun r beta => periodizeRow_periodic _ r beta
  set A : ℝ → ℝ → ℂ := rawD2StarMixed k with hA
  set D : ℝ → ℂ :=
    projectionMixedError (rawDiagonalPart (p 1) (periodizeRow k)) with hD
  have hAB : TorusBoundedTwo A := TorusBoundedThree.rawD2StarMixed hkB
  have hDB : TorusBoundedOne D :=
    torusBounded₁_projectionMixedError (hpkB.rawDiagonalPart (p 1))
  have hHeq : ∀ r beta : ℝ,
      rawD2StarMixed (rawOffDiagonalPart (p 1) (periodizeRow k)) r beta =
        A r beta - D beta := by
    intro r beta
    rw [rawD2StarMixed_rawOffDiagonalPart_eq hpkB hper (p 1) r beta,
      rawD2StarMixed_periodizeRow]
  have hHB : TorusBoundedTwo
      (rawD2StarMixed (rawOffDiagonalPart (p 1) (periodizeRow k))) :=
    TorusBoundedThree.rawD2StarMixed (torusBounded₃_rawOffDiagonalPart hpkB (p 1))
  have hbeta : ∀ r beta : ℝ, beta ∉ Icc (-q.rho) q.rho →
      rawD2StarMixed (rawOffDiagonalPart (p 1) (periodizeRow k)) r beta = 0 := by
    intro r beta hbeta
    have habs : q.rho / (8 * q.K) < |beta| := by
      rcases not_and_or.mp (fun h => hbeta ⟨h.1, h.2⟩) with h | h
      · have : beta < -q.rho := lt_of_not_ge h
        have : q.rho < |beta| := by
          rw [abs_of_neg (by linarith [hq.2.2.2.1])]
          linarith
        exact lt_of_le_of_lt (rho_div_le_rho hq) this
      · have hgt : q.rho < beta := lt_of_not_ge h
        have : q.rho < |beta| := by
          rw [abs_of_pos (by linarith [hq.2.2.2.1])]
          exact hgt
        exact lt_of_le_of_lt (rho_div_le_rho hq) this
    rw [hHeq r beta, hD,
      projectionMixedError_correction_eq_zero_of_beta hq ha habs, hA,
      rawD2StarMixed_correction_eq_zero_of_beta hq ha habs, sub_zero]
  have houter : (Estimates.torusIntegral fun s =>
        Estimates.torusIntegral fun beta =>
          intCharacter (-m) (p 1 + s) * intCharacter (-n) beta *
            rawD2StarMixed (rawOffDiagonalPart (p 1) (periodizeRow k))
              (p 1 + s) beta) =
      Estimates.torusIntegral fun r => Estimates.torusIntegral fun beta =>
        intCharacter (-m) r * intCharacter (-n) beta *
          rawD2StarMixed (rawOffDiagonalPart (p 1) (periodizeRow k)) r beta := by
    simp only [hHeq]
    refine torusIntegral_translate_row_sub_const hAB hDB (w := 2 * q.rho)
      (c := p 1) hwin1 ?_ m n
    intro r beta hr
    rw [hA]
    exact rawD2StarMixed_correction_eq_zero_of_row hq ha hp₂ hr
  rw [mixedFourierCoefficient_translate_of_outer (H :=
      rawD2StarMixed (rawOffDiagonalPart (p 1) (periodizeRow k)))
    (wb := q.rho) (c1 := p 1) (c2 := p 0) hwin2 hbeta m n houter]
  rw [mixedFourierCoefficient_correction hq.1 a p m n]
  have hone : intCharacter m (p 1) * intCharacter (-m) (p 1) = 1 := by
    rw [intCharacter_add_index]
    simp
  have htwo : intCharacter n (p 0) * intCharacter (-n) (p 0) = 1 := by
    rw [intCharacter_add_index]
    simp
  set Z : ℂ := Manhattan.type112DStarMixed p
    (Manhattan.shiftedCorrectionType112Coefficients (kappa := 40)
      (by norm_num) hq.1 a (p 0) (p 1))
    ⟨mixedPairFinset (m, n), isType12Index_mixedPairFinset m n⟩ with hZ
  linear_combination (intCharacter n (p 0) * intCharacter (-n) (p 0) * Z) * hone +
    Z * htwo

/-! ## The mixed sector symbol and its Fourier coefficients -/

theorem rawMixedTarget_measurable (q : Parameters) (a : ℝ) :
    Measurable (fun r => ((rawMixedTarget q a r : ℝ) : ℂ)) := by
  classical
  have : Measurable (rawMixedTarget q a) := by
    unfold rawMixedTarget Parameters.supportInterval
    exact Measurable.ite measurableSet_Icc measurable_const measurable_const
  exact Complex.measurable_ofReal.comp this

theorem norm_rawMixedTarget_le (q : Parameters) (a r : ℝ) :
    ‖((rawMixedTarget q a r : ℝ) : ℂ)‖ ≤ 1 := by
  classical
  rw [Complex.norm_real, Real.norm_eq_abs, rawMixedTarget]
  split_ifs <;> simp

theorem TorusBoundedTwo.shift {H : ℝ → ℝ → ℂ} (hH : TorusBoundedTwo H) (c1 c2 : ℝ) :
    TorusBoundedTwo fun s u => H (c1 + s) (c2 + u) := by
  obtain ⟨hm, C, hC⟩ := hH
  refine ⟨hm.comp ((measurable_const.add measurable_fst).prodMk
    (measurable_const.add measurable_snd)), C, fun s u => hC _ _⟩

/-- **The mixed degree-two frequency function of the corrected competitor.**
It is `sgn(sin p₁)` times the difference of the Lemma 4.1(c) target and the
projected mixed lowering symbol, read at the shifted frequencies. -/
def mixedSectorSymbol (q : Parameters) (p : Fin 2 → ℝ) (s u : ℝ) : ℂ :=
  (Real.sign (Real.sin (p 0)) : ℂ) *
      ((rawMixedTarget q |p 0| (p 1 + s) : ℝ) : ℂ) -
    (Real.sign (Real.sin (p 0)) : ℂ) *
      rawD2StarMixed (rawOffDiagonalPart (p 1)
        (periodizeRow (correctionCoefficient 40 q |p 0| (p 1)))) (p 1 + s) (p 0 + u)

theorem torusBounded₂_mixedSectorSymbol {q : Parameters} (hq : q.Admissible)
    (p : Fin 2 → ℝ) : TorusBoundedTwo (mixedSectorSymbol q p) := by
  have hsig : ‖((Real.sign (Real.sin (p 0)) : ℝ) : ℂ)‖ ≤ 1 := by
    rcases Real.sign_apply_eq (Real.sin (p 0)) with h | h | h <;> simp [h]
  have h1 : TorusBoundedTwo fun s _ : ℝ =>
      (Real.sign (Real.sin (p 0)) : ℂ) *
        ((rawMixedTarget q |p 0| (p 1 + s) : ℝ) : ℂ) := by
    refine ⟨measurable_const.mul (((rawMixedTarget_measurable q |p 0|).comp
      (measurable_const.add measurable_fst))), 1, fun s u => ?_⟩
    rw [norm_mul]
    calc ‖((Real.sign (Real.sin (p 0)) : ℝ) : ℂ)‖ *
        ‖((rawMixedTarget q |p 0| (p 1 + s) : ℝ) : ℂ)‖ ≤ 1 * 1 :=
          mul_le_mul hsig (norm_rawMixedTarget_le _ _ _) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hHB : TorusBoundedTwo (rawD2StarMixed (rawOffDiagonalPart (p 1)
      (periodizeRow (correctionCoefficient 40 q |p 0| (p 1))))) :=
    TorusBoundedThree.rawD2StarMixed (torusBounded₃_rawOffDiagonalPart
      (torusBounded₃_periodizeRow
        (torusBounded₃_correctionCoefficient (by norm_num) hq.1 |p 0| (p 1))) (p 1))
  obtain ⟨hm2, C2, hC2⟩ := hHB.shift (p 1) (p 0)
  have h2 : TorusBoundedTwo fun s u : ℝ =>
      (Real.sign (Real.sin (p 0)) : ℂ) *
        rawD2StarMixed (rawOffDiagonalPart (p 1)
          (periodizeRow (correctionCoefficient 40 q |p 0| (p 1))))
          (p 1 + s) (p 0 + u) := by
    have hC2nn : 0 ≤ C2 := le_trans (norm_nonneg _) (hC2 0 0)
    refine ⟨measurable_const.mul hm2, C2, fun s u => ?_⟩
    rw [norm_mul]
    calc ‖((Real.sign (Real.sin (p 0)) : ℝ) : ℂ)‖ *
        ‖rawD2StarMixed (rawOffDiagonalPart (p 1)
          (periodizeRow (correctionCoefficient 40 q |p 0| (p 1))))
          (p 1 + s) (p 0 + u)‖ ≤ 1 * C2 :=
          mul_le_mul hsig (hC2 s u) (norm_nonneg _) zero_le_one
      _ = C2 := one_mul C2
  obtain ⟨hm1, C1, hC1⟩ := h1
  obtain ⟨hm2', C2', hC2'⟩ := h2
  refine ⟨hm1.sub hm2', C1 + C2', fun s u => ?_⟩
  exact le_trans (norm_sub_le _ _) (add_le_add (hC1 s u) (hC2' s u))

theorem torusBounded₂_charMul₂₂ {H : ℝ → ℝ → ℂ} (hH : TorusBoundedTwo H) (m n : ℤ) :
    TorusBoundedTwo fun s u => intCharacter (-m) s * intCharacter (-n) u * H s u := by
  obtain ⟨hm, C, hC⟩ := hH
  refine ⟨((((measurable_intCharacter (-m)).comp measurable_fst).mul
    ((measurable_intCharacter (-n)).comp measurable_snd))).mul hm, C, fun s u => ?_⟩
  rw [norm_mul, norm_mul, norm_intCharacter, norm_intCharacter, one_mul, one_mul]
  exact hC s u

theorem torusIntegral₂_char_sub {F G : ℝ → ℝ → ℂ} (hF : TorusBoundedTwo F)
    (hG : TorusBoundedTwo G) (m n : ℤ) :
    (Estimates.torusIntegral fun s => Estimates.torusIntegral fun u =>
        intCharacter (-m) s * intCharacter (-n) u * (F s u - G s u)) =
      (Estimates.torusIntegral fun s => Estimates.torusIntegral fun u =>
        intCharacter (-m) s * intCharacter (-n) u * F s u) -
      (Estimates.torusIntegral fun s => Estimates.torusIntegral fun u =>
        intCharacter (-m) s * intCharacter (-n) u * G s u) := by
  have hFc := torusBounded₂_charMul₂₂ hF m n
  have hGc := torusBounded₂_charMul₂₂ hG m n
  have hinner : ∀ s : ℝ,
      (Estimates.torusIntegral fun u =>
        intCharacter (-m) s * intCharacter (-n) u * (F s u - G s u)) =
      (Estimates.torusIntegral fun u =>
        intCharacter (-m) s * intCharacter (-n) u * F s u) -
      (Estimates.torusIntegral fun u =>
        intCharacter (-m) s * intCharacter (-n) u * G s u) := by
    intro s
    have hpt : ∀ u : ℝ,
        intCharacter (-m) s * intCharacter (-n) u * (F s u - G s u) =
          intCharacter (-m) s * intCharacter (-n) u * F s u -
            intCharacter (-m) s * intCharacter (-n) u * G s u := by
      intro u; ring
    simp only [hpt]
    exact torusIntegral_sub (hFc.integrable_right s) (hGc.integrable_right s)
  simp only [hinner]
  exact torusIntegral_sub hFc.integral_right.integrable hGc.integral_right.integrable

/-- **The Fourier coefficients of the mixed sector symbol.** -/
theorem mFourierCoeff_mixedSectorSymbol {q : Parameters} (hq : q.Admissible)
    {p : Fin 2 → ℝ} (hp₂ : |p 1| ≤ |p 0|)
    (hwin1 : 2 * q.rho + |p 1| < Real.pi) (hwin2 : q.rho + |p 0| < Real.pi)
    (hf : MemLp (degreeOneCoefficient q (p 0)) 2
      (volume.restrict (Ioc (-Real.pi) Real.pi))) (m n : ℤ) :
    (Estimates.torusIntegral fun s => Estimates.torusIntegral fun u =>
        intCharacter (-m) s * intCharacter (-n) u * mixedSectorSymbol q p s u) =
      (if n = 0 then
        (2 : ℂ)⁻¹ *
          (Complex.exp (Complex.I * (p 1 : ℂ)) *
              fourierBasis.repr (rowTorusShift (p 1)
                (Manhattan.realTorusL2 (degreeOneCoefficient q (p 0)) hf)) (m - 1) -
            Complex.exp (-Complex.I * (p 1 : ℂ)) *
              fourierBasis.repr (rowTorusShift (p 1)
                (Manhattan.realTorusL2 (degreeOneCoefficient q (p 0)) hf)) (m + 1))
      else 0) -
        (Real.sign (Real.sin (p 0)) : ℂ) *
          Manhattan.type112DStarMixed p
            (Manhattan.shiftedCorrectionType112Coefficients (kappa := 40)
              (by norm_num) hq.1 |p 0| (p 0) (p 1))
            ⟨mixedPairFinset (m, n), isType12Index_mixedPairFinset m n⟩ := by
  have hsig : ‖((Real.sign (Real.sin (p 0)) : ℝ) : ℂ)‖ ≤ 1 := by
    rcases Real.sign_apply_eq (Real.sin (p 0)) with h | h | h <;> simp [h]
  have h1 : TorusBoundedTwo fun s _ : ℝ =>
      (Real.sign (Real.sin (p 0)) : ℂ) *
        ((rawMixedTarget q |p 0| (p 1 + s) : ℝ) : ℂ) := by
    refine ⟨measurable_const.mul (((rawMixedTarget_measurable q |p 0|).comp
      (measurable_const.add measurable_fst))), 1, fun s u => ?_⟩
    rw [norm_mul]
    calc ‖((Real.sign (Real.sin (p 0)) : ℝ) : ℂ)‖ *
        ‖((rawMixedTarget q |p 0| (p 1 + s) : ℝ) : ℂ)‖ ≤ 1 * 1 :=
          mul_le_mul hsig (norm_rawMixedTarget_le _ _ _) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hHB : TorusBoundedTwo (rawD2StarMixed (rawOffDiagonalPart (p 1)
      (periodizeRow (correctionCoefficient 40 q |p 0| (p 1))))) :=
    TorusBoundedThree.rawD2StarMixed (torusBounded₃_rawOffDiagonalPart
      (torusBounded₃_periodizeRow
        (torusBounded₃_correctionCoefficient (by norm_num) hq.1 |p 0| (p 1))) (p 1))
  have hHs := hHB.shift (p 1) (p 0)
  have h2 : TorusBoundedTwo fun s u : ℝ =>
      (Real.sign (Real.sin (p 0)) : ℂ) *
        rawD2StarMixed (rawOffDiagonalPart (p 1)
          (periodizeRow (correctionCoefficient 40 q |p 0| (p 1))))
          (p 1 + s) (p 0 + u) := by
    obtain ⟨hm2, C2, hC2⟩ := hHs
    have hC2nn : 0 ≤ C2 := le_trans (norm_nonneg _) (hC2 0 0)
    refine ⟨measurable_const.mul hm2, C2, fun s u => ?_⟩
    rw [norm_mul]
    calc ‖((Real.sign (Real.sin (p 0)) : ℝ) : ℂ)‖ *
        ‖rawD2StarMixed (rawOffDiagonalPart (p 1)
          (periodizeRow (correctionCoefficient 40 q |p 0| (p 1))))
          (p 1 + s) (p 0 + u)‖ ≤ 1 * C2 :=
          mul_le_mul hsig (hC2 s u) (norm_nonneg _) zero_le_one
      _ = C2 := one_mul C2
  simp only [mixedSectorSymbol]
  rw [torusIntegral₂_char_sub
      (F := fun s _ : ℝ => (Real.sign (Real.sin (p 0)) : ℂ) *
        ((rawMixedTarget q |p 0| (p 1 + s) : ℝ) : ℂ))
      (G := fun s u : ℝ => (Real.sign (Real.sin (p 0)) : ℂ) *
        rawD2StarMixed (rawOffDiagonalPart (p 1)
          (periodizeRow (correctionCoefficient 40 q |p 0| (p 1))))
          (p 1 + s) (p 0 + u)) h1 h2 m n,
    raisingHalf_fourierCoeff hq hwin1 hf m n]
  congr 1
  have hpull : ∀ s : ℝ,
      (Estimates.torusIntegral fun u =>
        intCharacter (-m) s * intCharacter (-n) u *
          ((Real.sign (Real.sin (p 0)) : ℂ) *
            rawD2StarMixed (rawOffDiagonalPart (p 1)
              (periodizeRow (correctionCoefficient 40 q |p 0| (p 1))))
              (p 1 + s) (p 0 + u))) =
      (Real.sign (Real.sin (p 0)) : ℂ) *
        Estimates.torusIntegral fun u =>
          intCharacter (-m) s * intCharacter (-n) u *
            rawD2StarMixed (rawOffDiagonalPart (p 1)
              (periodizeRow (correctionCoefficient 40 q |p 0| (p 1))))
              (p 1 + s) (p 0 + u) := by
    intro s
    rw [← torusIntegral_const_mul]
    congr 1
    funext u
    ring
  simp only [hpull]
  rw [torusIntegral_const_mul, loweringHalf_fourierCoeff hq hp₂ hwin1 hwin2 m n]

theorem type112DStarMixed_smul (p : Fin 2 → ℝ) (z : ℂ)
    (c : ℓ²(Manhattan.Type112Index, ℂ)) :
    Manhattan.type112DStarMixed p (z • c) =
      z • Manhattan.type112DStarMixed p c := by
  have hL : ∀ T : Manhattan.Type12Index,
      Manhattan.type112DStarMixed p (z • c) T =
        z * Manhattan.type112DStarMixed p c T := by
    intro T
    rw [Manhattan.type112DStarMixed_apply, Manhattan.type112DStarMixed_apply,
      map_smul, inner_smul_right]
  apply lp.ext
  funext T
  simpa using hL T

theorem mixedSectorCoefficient_apply (p : Fin 2 → ℝ)
    (c : Manhattan.RowLineCoefficient) (kc : ℓ²(Manhattan.Type112Index, ℂ))
    (m n : ℤ) :
    (Manhattan.type12WalshAnalysis
          (walshRaise p (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal c)) -
        Manhattan.type112DStarMixed p kc)
        ⟨mixedPairFinset (m, n), isType12Index_mixedPairFinset m n⟩ =
      (if n = 0 then
        (2 : ℂ)⁻¹ *
          (Complex.exp (Complex.I * (p 1 : ℂ)) * c (m - 1) -
            Complex.exp (-Complex.I * (p 1 : ℂ)) * c (m + 1))
      else 0) -
        Manhattan.type112DStarMixed p kc
          ⟨mixedPairFinset (m, n), isType12Index_mixedPairFinset m n⟩ := by
  have hsub : (Manhattan.type12WalshAnalysis
        (walshRaise p (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal c)) -
      Manhattan.type112DStarMixed p kc)
        ⟨mixedPairFinset (m, n), isType12Index_mixedPairFinset m n⟩ =
      Manhattan.type12WalshAnalysis
          (walshRaise p (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal c))
          ⟨mixedPairFinset (m, n), isType12Index_mixedPairFinset m n⟩ -
        Manhattan.type112DStarMixed p kc
          ⟨mixedPairFinset (m, n), isType12Index_mixedPairFinset m n⟩ := rfl
  rw [hsub, Manhattan.type12WalshAnalysis, Manhattan.walshSectorAnalysis_apply,
    inner_mixedPair_walshRaise_axisDegreeOne p c m n]

/-- **The mixed sector symbol is the frequency function of the mixed sector.**
Its two-dimensional Fourier coefficients are the mixed Walsh coefficients of
`D₁f_p - D₂*k_p`. -/
theorem mFourierCoeff_mixedSectorSymbol_eq_coeff {q : Parameters} (hq : q.Admissible)
    {p : Fin 2 → ℝ} (hp₂ : |p 1| ≤ |p 0|)
    (hwin1 : 2 * q.rho + |p 1| < Real.pi) (hwin2 : q.rho + |p 0| < Real.pi)
    (hcert : LemmaFourTwoIntegralCertificate q (p 0) (p 1))
    (hnormalization : degreeOneNormalization q (p 0) ≠ 0)
    (S : Manhattan.Type12Index) :
    UnitAddTorus.mFourierCoeff
        ((mixedAngleL2 (torusBounded₂_mixedSectorSymbol hq p) :
          UnitAddTorus (Fin 2) → ℂ)) (type12RawIndex S) =
      (Manhattan.type12WalshAnalysis
          (walshRaise p (correctedRowVector
            (correctedLowDegreeData hq.1 p hcert hnormalization))) -
        Manhattan.type112DStarMixed p
          (correctedLowDegreeData hq.1 p hcert hnormalization).mixedCoefficient) S := by
  classical
  have hf : MemLp (degreeOneCoefficient q (p 0)) 2
      (volume.restrict (Ioc (-Real.pi) Real.pi)) := by
    simpa only [Estimates.torus] using
      degreeOneCoefficient_memLp_of_integralCertificate hq.1 hcert
  have hS : S = ⟨mixedPairFinset (type12RawIndex S 0, type12RawIndex S 1),
      isType12Index_mixedPairFinset _ _⟩ :=
    Subtype.ext (mixedPairFinset_type12RawIndex S).symm
  rw [mFourierCoeff_mixedAngleL2,
    mFourierCoeff_mixedSectorSymbol hq hp₂ hwin1 hwin2 hf
      (type12RawIndex S 0) (type12RawIndex S 1)]
  rw [correctedRowVector_eq_axisDegreeOneSynthesis,
    correctedLowDegreeData_row_eq hq.1 p hcert hnormalization]
  conv_rhs => rw [hS]
  rw [mixedSectorCoefficient_apply,
    correctedLowDegreeData_mixedCoefficient_eq hq.1 p hcert hnormalization,
    type112DStarMixed_smul]
  rfl

theorem type12RawIndex_surjective : Function.Surjective type12RawIndex := by
  intro v
  refine ⟨mixedPairEquiv (v 0, v 1), ?_⟩
  rw [type12RawIndex, mixedPairEquiv.symm_apply_apply]
  funext i
  fin_cases i <;> simp

/-- **The frequency function of the mixed sector.** -/
theorem type12FreqFun_mixedSector {q : Parameters} (hq : q.Admissible)
    {p : Fin 2 → ℝ} (hp₂ : |p 1| ≤ |p 0|)
    (hwin1 : 2 * q.rho + |p 1| < Real.pi) (hwin2 : q.rho + |p 0| < Real.pi)
    (hcert : LemmaFourTwoIntegralCertificate q (p 0) (p 1))
    (hnormalization : degreeOneNormalization q (p 0) ≠ 0) :
    type12FreqFun
        (Manhattan.type12WalshAnalysis
            (walshRaise p (correctedRowVector
              (correctedLowDegreeData hq.1 p hcert hnormalization))) -
          Manhattan.type112DStarMixed p
            (correctedLowDegreeData hq.1 p hcert hnormalization).mixedCoefficient) =
      mixedAngleL2 (torusBounded₂_mixedSectorSymbol hq p) := by
  refine type12FreqFun_eq_of_mFourierCoeff _ _ ?_ ?_
  · intro S
    exact mFourierCoeff_mixedSectorSymbol_eq_coeff hq hp₂ hwin1 hwin2 hcert
      hnormalization S
  · intro v hv
    obtain ⟨S, hS⟩ := type12RawIndex_surjective v
    exact absurd hS (hv S)

/-- **The mixed sector energy of summand 3, as an iterated torus integral.** -/
theorem hMinusEnergy_mixedSector {q : Parameters} (hq : q.Admissible)
    {p : Fin 2 → ℝ} (hp₂ : |p 1| ≤ |p 0|)
    (hwin1 : 2 * q.rho + |p 1| < Real.pi) (hwin2 : q.rho + |p 0| < Real.pi)
    (hcert : LemmaFourTwoIntegralCertificate q (p 0) (p 1))
    (hnormalization : degreeOneNormalization q (p 0) ≠ 0) :
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hq.1
        (Manhattan.type12WalshSynthesis
          (Manhattan.type12WalshAnalysis
              (walshRaise p (correctedRowVector
                (correctedLowDegreeData hq.1 p hcert hnormalization))) -
            Manhattan.type112DStarMixed p
              (correctedLowDegreeData hq.1 p hcert hnormalization).mixedCoefficient)) =
      Estimates.torusIntegral fun s => Estimates.torusIntegral fun u =>
        mixedHMinusWeight q (p 1 + s) (p 0 + u) *
          ‖mixedSectorSymbol q p s u‖ ^ 2 := by
  obtain ⟨hmeas, M, hM⟩ := torusBounded₂_mixedSectorSymbol hq p
  refine hMinusEnergy_type12WalshSynthesis_torusIntegral hq.1 p _
    (mixedSectorSymbol q p) hmeas hM ?_
  rw [type12FreqFun_mixedSector hq hp₂ hwin1 hwin2 hcert hnormalization]
  exact coeFn_mixedAngleL2 (torusBounded₂_mixedSectorSymbol hq p)

/-! ## The mixed `H⁻¹` weight and translation of energies -/

theorem mixedHMinusWeight_periodic_left (q : Parameters) (beta : ℝ) :
    Function.Periodic (fun r => mixedHMinusWeight q r beta) (2 * Real.pi) := by
  intro r
  simp only [mixedHMinusWeight, dispersion_periodic r]

theorem mixedHMinusWeight_periodic_right (q : Parameters) (r : ℝ) :
    Function.Periodic (fun beta => mixedHMinusWeight q r beta) (2 * Real.pi) := by
  intro beta
  simp only [mixedHMinusWeight, dispersion_periodic beta]

theorem mixedHMinusWeight_pos {q : Parameters} (hlam : 0 < q.lambda) (r beta : ℝ) :
    0 < mixedHMinusWeight q r beta := by
  rw [mixedHMinusWeight]
  exact inv_pos.mpr (mixed_denominator_pos hlam r beta)

theorem mixedHMinusWeight_le {q : Parameters} (hlam : 0 < q.lambda) (r beta : ℝ) :
    mixedHMinusWeight q r beta ≤ q.lambda⁻¹ := by
  rw [mixedHMinusWeight]
  refine (inv_le_inv₀ (mixed_denominator_pos hlam r beta) hlam).2 ?_
  linarith [dispersion_nonneg r, dispersion_nonneg beta]

theorem measurable_mixedHMinusWeight (q : Parameters) :
    Measurable fun z : ℝ × ℝ => mixedHMinusWeight q z.1 z.2 := by
  unfold mixedHMinusWeight Estimates.dispersion
  fun_prop

/-- Translation invariance for a function which splits as a supported part plus
a periodic part. -/
theorem torusIntegral_translate_split {h1 h2 : ℝ → ℝ} {c w : ℝ}
    (hw : w + |c| < Real.pi)
    (hm1 : Measurable h1) {C1 : ℝ} (hb1 : ∀ x, |h1 x| ≤ C1)
    (hm2 : Measurable h2) {C2 : ℝ} (hb2 : ∀ x, |h2 x| ≤ C2)
    (hsupp : ∀ s, s ∉ Icc (-w) w → h1 s = 0)
    (hper : Function.Periodic h2 (2 * Real.pi)) :
    (Estimates.torusIntegral fun x => h1 (c + x) + h2 (c + x)) =
      Estimates.torusIntegral fun x => h1 x + h2 x := by
  have hi1 : Integrable h1 (volume.restrict Estimates.torus) :=
    integrable_torus_of_bound hm1.aestronglyMeasurable
      (fun x => by simpa [Real.norm_eq_abs] using hb1 x)
  have hi2 : Integrable h2 (volume.restrict Estimates.torus) :=
    integrable_torus_of_bound hm2.aestronglyMeasurable
      (fun x => by simpa [Real.norm_eq_abs] using hb2 x)
  have hi1' : Integrable (fun x => h1 (c + x)) (volume.restrict Estimates.torus) :=
    integrable_torus_of_bound
      (hm1.comp (measurable_const.add measurable_id)).aestronglyMeasurable
      (fun x => by simpa [Real.norm_eq_abs] using hb1 (c + x))
  have hi2' : Integrable (fun x => h2 (c + x)) (volume.restrict Estimates.torus) :=
    integrable_torus_of_bound
      (hm2.comp (measurable_const.add measurable_id)).aestronglyMeasurable
      (fun x => by simpa [Real.norm_eq_abs] using hb2 (c + x))
  rw [torusIntegral_add hi1' hi2', torusIntegral_add hi1 hi2,
    torusIntegral_translate_window (E := ℝ) (h := h1) (c := c) (w := w) hw hsupp,
    torusIntegral_translate_periodic (E := ℝ) (h := h2) hper c]

theorem torusBounded₂_mixedRawResidual {q : Parameters} (hq : q.Admissible)
    (a p₂ : ℝ) : TorusBoundedTwo (mixedRawResidual q a p₂) := by
  have hA : TorusBoundedTwo (rawD2StarMixed (correctionCoefficient 40 q a p₂)) :=
    TorusBoundedThree.rawD2StarMixed
      (torusBounded₃_correctionCoefficient (by norm_num) hq.1 a p₂)
  obtain ⟨hmA, CA, hCA⟩ := hA
  refine ⟨?_, 1 + CA, fun r beta => ?_⟩
  · exact ((rawMixedTarget_measurable q a).comp measurable_fst).sub hmA
  · rw [mixedRawResidual]
    exact le_trans (norm_sub_le _ _)
      (add_le_add (norm_rawMixedTarget_le _ _ _) (hCA r beta))


section EnergyTranslate

variable {q : Parameters}

theorem measurable_weight_norm_sq {F : ℝ → ℝ → ℂ} (hF : Measurable fun z : ℝ × ℝ => F z.1 z.2)
    (q : Parameters) :
    Measurable fun z : ℝ × ℝ => mixedHMinusWeight q z.1 z.2 * ‖F z.1 z.2‖ ^ 2 :=
  (measurable_mixedHMinusWeight q).mul (hF.norm.pow_const 2)

theorem abs_weight_norm_sq_le {F : ℝ → ℝ → ℂ} (hlam : 0 < q.lambda) {C : ℝ}
    (hC : ∀ r beta, ‖F r beta‖ ≤ C) (r beta : ℝ) :
    |mixedHMinusWeight q r beta * ‖F r beta‖ ^ 2| ≤ q.lambda⁻¹ * C ^ 2 := by
  have hCnn : 0 ≤ C := le_trans (norm_nonneg _) (hC 0 0)
  have hw := mixedHMinusWeight_pos hlam r beta
  have hwle := mixedHMinusWeight_le hlam r beta
  have hsq : ‖F r beta‖ ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hC r beta) 2
  rw [abs_of_nonneg (by positivity)]
  exact mul_le_mul hwle hsq (sq_nonneg _) (by positivity)

/-- **The `(s,u) → (r,β)` translation of the mixed scalar energy.** -/
theorem mixedRawResidual_energy_translate (hq : q.Admissible)
    {a p₂ c1 c2 : ℝ} (ha : 0 ≤ a) (hp₂ : |p₂| ≤ a)
    (hw1 : 2 * q.rho + |c1| < Real.pi) (hw2 : q.rho + |c2| < Real.pi) :
    (Estimates.torusIntegral fun s => Estimates.torusIntegral fun u =>
        mixedHMinusWeight q (c1 + s) (c2 + u) *
          ‖mixedRawResidual q a p₂ (c1 + s) (c2 + u)‖ ^ 2) =
      mixedRawResidualHMinusSq q a p₂ := by
  obtain ⟨hmM, CM, hCM⟩ := torusBounded₂_mixedRawResidual hq a p₂
  have hlam := hq.1
  have hrhopos : 0 < q.rho := hq.2.2.2.1
  have hmeas2 : Measurable fun z : ℝ × ℝ =>
      mixedHMinusWeight q z.1 z.2 * ‖mixedRawResidual q a p₂ z.1 z.2‖ ^ 2 :=
    measurable_weight_norm_sq hmM q
  have hbeta : ∀ r beta : ℝ, beta ∉ Icc (-q.rho) q.rho →
      mixedRawResidual q a p₂ r beta = ((rawMixedTarget q a r : ℝ) : ℂ) := by
    intro r beta hb
    have habs : q.rho / (8 * q.K) < |beta| := by
      rcases not_and_or.mp (fun h => hb ⟨h.1, h.2⟩) with h | h
      · have h1 : beta < -q.rho := lt_of_not_ge h
        have h2 : q.rho < |beta| := by
          rw [abs_of_neg (by linarith)]; linarith
        exact lt_of_le_of_lt (rho_div_le_rho hq) h2
      · have h1 : q.rho < beta := lt_of_not_ge h
        have h2 : q.rho < |beta| := by rw [abs_of_pos (by linarith)]; exact h1
        exact lt_of_le_of_lt (rho_div_le_rho hq) h2
    rw [mixedRawResidual, rawD2StarMixed_correction_eq_zero_of_beta hq ha habs,
      sub_zero]
  have hinner : ∀ r : ℝ,
      (Estimates.torusIntegral fun u =>
        mixedHMinusWeight q r (c2 + u) * ‖mixedRawResidual q a p₂ r (c2 + u)‖ ^ 2) =
      Estimates.torusIntegral fun beta =>
        mixedHMinusWeight q r beta * ‖mixedRawResidual q a p₂ r beta‖ ^ 2 := by
    intro r
    have e1 : (fun u => mixedHMinusWeight q r (c2 + u) *
          ‖mixedRawResidual q a p₂ r (c2 + u)‖ ^ 2) =
        fun u => (mixedHMinusWeight q r (c2 + u) *
              ‖mixedRawResidual q a p₂ r (c2 + u)‖ ^ 2 -
            mixedHMinusWeight q r (c2 + u) *
              ‖((rawMixedTarget q a r : ℝ) : ℂ)‖ ^ 2) +
          mixedHMinusWeight q r (c2 + u) *
            ‖((rawMixedTarget q a r : ℝ) : ℂ)‖ ^ 2 := by
      funext u; ring
    have e2 : (fun beta => mixedHMinusWeight q r beta *
          ‖mixedRawResidual q a p₂ r beta‖ ^ 2) =
        fun beta => (mixedHMinusWeight q r beta *
              ‖mixedRawResidual q a p₂ r beta‖ ^ 2 -
            mixedHMinusWeight q r beta *
              ‖((rawMixedTarget q a r : ℝ) : ℂ)‖ ^ 2) +
          mixedHMinusWeight q r beta *
            ‖((rawMixedTarget q a r : ℝ) : ℂ)‖ ^ 2 := by
      funext beta; ring
    rw [e1, e2]
    refine torusIntegral_translate_split (w := q.rho) (c := c2) hw2
      (h1 := fun beta => mixedHMinusWeight q r beta *
          ‖mixedRawResidual q a p₂ r beta‖ ^ 2 -
        mixedHMinusWeight q r beta * ‖((rawMixedTarget q a r : ℝ) : ℂ)‖ ^ 2)
      (h2 := fun beta => mixedHMinusWeight q r beta *
        ‖((rawMixedTarget q a r : ℝ) : ℂ)‖ ^ 2)
      ?_ (C1 := q.lambda⁻¹ * CM ^ 2 + q.lambda⁻¹ * 1 ^ 2) ?_
      ?_ (C2 := q.lambda⁻¹ * 1 ^ 2) ?_ ?_ ?_
    · exact ((measurable_mixedHMinusWeight q).comp
        (measurable_const.prodMk measurable_id)).mul
        ((hmM.comp (measurable_const.prodMk measurable_id)).norm.pow_const 2) |>.sub
        (((measurable_mixedHMinusWeight q).comp
          (measurable_const.prodMk measurable_id)).mul measurable_const)
    · intro beta
      refine le_trans (abs_sub _ _) (add_le_add ?_ ?_)
      · exact abs_weight_norm_sq_le (F := mixedRawResidual q a p₂) hlam hCM r beta
      · exact abs_weight_norm_sq_le (F := fun r _ => ((rawMixedTarget q a r : ℝ) : ℂ))
          hlam (fun r' _ => norm_rawMixedTarget_le q a r') r beta
    · exact ((measurable_mixedHMinusWeight q).comp
        (measurable_const.prodMk measurable_id)).mul measurable_const
    · intro beta
      exact abs_weight_norm_sq_le (F := fun r _ => ((rawMixedTarget q a r : ℝ) : ℂ))
        hlam (fun r' _ => norm_rawMixedTarget_le q a r') r beta
    · intro beta hb
      show mixedHMinusWeight q r beta * ‖mixedRawResidual q a p₂ r beta‖ ^ 2 -
        mixedHMinusWeight q r beta * ‖((rawMixedTarget q a r : ℝ) : ℂ)‖ ^ 2 = 0
      rw [hbeta r beta hb, sub_self]
    · intro beta
      show mixedHMinusWeight q r (beta + 2 * Real.pi) *
          ‖((rawMixedTarget q a r : ℝ) : ℂ)‖ ^ 2 =
        mixedHMinusWeight q r beta * ‖((rawMixedTarget q a r : ℝ) : ℂ)‖ ^ 2
      congr 1
      exact mixedHMinusWeight_periodic_right q r beta
  simp only [hinner]
  rw [torusIntegral_translate_window (E := ℝ)
    (h := fun r => Estimates.torusIntegral fun beta =>
      mixedHMinusWeight q r beta * ‖mixedRawResidual q a p₂ r beta‖ ^ 2)
    (c := c1) (w := 2 * q.rho) hw1 ?_]
  · rw [mixedRawResidualHMinusSq]
    exact torusIntegral₂_swap hmeas2
      (fun r beta => abs_weight_norm_sq_le (F := mixedRawResidual q a p₂) hlam hCM r beta)
  · intro r hr
    show (Estimates.torusIntegral fun beta =>
      mixedHMinusWeight q r beta * ‖mixedRawResidual q a p₂ r beta‖ ^ 2) = 0
    have hz : (fun beta => mixedHMinusWeight q r beta *
        ‖mixedRawResidual q a p₂ r beta‖ ^ 2) = fun _ : ℝ => (0 : ℝ) := by
      funext beta
      rw [mixedRawResidual_eq_zero_of_row hq ha hp₂ hr]
      simp
    rw [hz, torusIntegral_const]

end EnergyTranslate

/-- **The `(s,u) → (r,β)` translation of the coincident-row energy.** -/
theorem projectionError_energy_translate {q : Parameters} (hq : q.Admissible)
    {a p₂ c1 c2 : ℝ} (ha : 0 ≤ a) (hw2 : q.rho + |c2| < Real.pi) :
    (Estimates.torusIntegral fun s => Estimates.torusIntegral fun u =>
        mixedHMinusWeight q (c1 + s) (c2 + u) *
          ‖projectionMixedError (rawDiagonalPart p₂ (periodizeRow
            (correctionCoefficient 40 q a p₂))) (c2 + u)‖ ^ 2) =
      projectionErrorHMinusSq q (rawDiagonalPart p₂ (periodizeRow
        (correctionCoefficient 40 q a p₂))) := by
  have hlam := hq.1
  have hrhopos : 0 < q.rho := hq.2.2.2.1
  obtain ⟨hmD, CD, hCD⟩ := torusBounded₁_projectionMixedError
    ((torusBounded₃_periodizeRow
      (torusBounded₃_correctionCoefficient (by norm_num : (0:ℝ) < 40) hlam a p₂)).rawDiagonalPart p₂)
  have hDzero : ∀ beta : ℝ, beta ∉ Icc (-q.rho) q.rho →
      projectionMixedError (rawDiagonalPart p₂ (periodizeRow
        (correctionCoefficient 40 q a p₂))) beta = 0 := by
    intro beta hb
    have habs : q.rho / (8 * q.K) < |beta| := by
      rcases not_and_or.mp (fun h => hb ⟨h.1, h.2⟩) with h | h
      · have h1 : beta < -q.rho := lt_of_not_ge h
        have h2 : q.rho < |beta| := by rw [abs_of_neg (by linarith)]; linarith
        exact lt_of_le_of_lt (rho_div_le_rho hq) h2
      · have h1 : q.rho < beta := lt_of_not_ge h
        have h2 : q.rho < |beta| := by rw [abs_of_pos (by linarith)]; exact h1
        exact lt_of_le_of_lt (rho_div_le_rho hq) h2
    exact projectionMixedError_correction_eq_zero_of_beta hq ha habs
  have hmeas2 : Measurable fun z : ℝ × ℝ =>
      mixedHMinusWeight q z.1 z.2 *
        ‖projectionMixedError (rawDiagonalPart p₂ (periodizeRow
          (correctionCoefficient 40 q a p₂))) z.2‖ ^ 2 :=
    measurable_weight_norm_sq (F := fun _ beta =>
      projectionMixedError (rawDiagonalPart p₂ (periodizeRow
        (correctionCoefficient 40 q a p₂))) beta) (hmD.comp measurable_snd) q
  have hbnd : ∀ r beta : ℝ,
      |mixedHMinusWeight q r beta *
        ‖projectionMixedError (rawDiagonalPart p₂ (periodizeRow
          (correctionCoefficient 40 q a p₂))) beta‖ ^ 2| ≤ q.lambda⁻¹ * CD ^ 2 :=
    fun r beta => abs_weight_norm_sq_le (F := fun _ b =>
      projectionMixedError (rawDiagonalPart p₂ (periodizeRow
        (correctionCoefficient 40 q a p₂))) b) hlam (fun _ b => hCD b) r beta
  have hinner : ∀ r : ℝ,
      (Estimates.torusIntegral fun u =>
        mixedHMinusWeight q r (c2 + u) *
          ‖projectionMixedError (rawDiagonalPart p₂ (periodizeRow
            (correctionCoefficient 40 q a p₂))) (c2 + u)‖ ^ 2) =
      Estimates.torusIntegral fun beta =>
        mixedHMinusWeight q r beta *
          ‖projectionMixedError (rawDiagonalPart p₂ (periodizeRow
            (correctionCoefficient 40 q a p₂))) beta‖ ^ 2 := by
    intro r
    refine torusIntegral_translate_window (E := ℝ)
      (h := fun beta => mixedHMinusWeight q r beta *
        ‖projectionMixedError (rawDiagonalPart p₂ (periodizeRow
          (correctionCoefficient 40 q a p₂))) beta‖ ^ 2)
      (c := c2) (w := q.rho) hw2 ?_
    intro beta hb
    show mixedHMinusWeight q r beta *
      ‖projectionMixedError (rawDiagonalPart p₂ (periodizeRow
        (correctionCoefficient 40 q a p₂))) beta‖ ^ 2 = 0
    rw [hDzero beta hb]
    simp
  simp only [hinner]
  rw [torusIntegral_translate_periodic (E := ℝ)
    (h := fun r => Estimates.torusIntegral fun beta =>
      mixedHMinusWeight q r beta *
        ‖projectionMixedError (rawDiagonalPart p₂ (periodizeRow
          (correctionCoefficient 40 q a p₂))) beta‖ ^ 2) ?_ c1]
  · rw [projectionErrorHMinusSq]
    exact torusIntegral₂_swap hmeas2 hbnd
  · intro r
    show (Estimates.torusIntegral fun beta =>
        mixedHMinusWeight q (r + 2 * Real.pi) beta *
          ‖projectionMixedError (rawDiagonalPart p₂ (periodizeRow
            (correctionCoefficient 40 q a p₂))) beta‖ ^ 2) =
      Estimates.torusIntegral fun beta =>
        mixedHMinusWeight q r beta *
          ‖projectionMixedError (rawDiagonalPart p₂ (periodizeRow
            (correctionCoefficient 40 q a p₂))) beta‖ ^ 2
    refine congrArg _ ?_
    funext beta
    congr 1
    exact mixedHMinusWeight_periodic_left q beta r

/-- The mixed sector symbol is `sgn(sin p₁)` times the scalar residual of
Lemma 5.4 plus the coincident-row mode dropped by the concrete lowering. -/
theorem mixedSectorSymbol_eq {q : Parameters} (hq : q.Admissible)
    (p : Fin 2 → ℝ) (s u : ℝ) :
    mixedSectorSymbol q p s u =
      (Real.sign (Real.sin (p 0)) : ℂ) *
        (mixedRawResidual q |p 0| (p 1) (p 1 + s) (p 0 + u) +
          projectionMixedError (rawDiagonalPart (p 1)
            (periodizeRow (correctionCoefficient 40 q |p 0| (p 1)))) (p 0 + u)) := by
  have hkB : TorusBoundedThree (periodizeRow (correctionCoefficient 40 q |p 0| (p 1))) :=
    torusBounded₃_periodizeRow
      (torusBounded₃_correctionCoefficient (by norm_num : (0:ℝ) < 40) hq.1 |p 0| (p 1))
  have hper : ∀ r beta : ℝ, Function.Periodic
      (fun r' => periodizeRow (correctionCoefficient 40 q |p 0| (p 1)) r r' beta)
      (2 * Real.pi) := fun r beta => periodizeRow_periodic _ r beta
  rw [mixedSectorSymbol,
    rawD2StarMixed_rawOffDiagonalPart_eq hkB hper (p 1) (p 1 + s) (p 0 + u),
    rawD2StarMixed_periodizeRow, mixedRawResidual]
  ring

theorem norm_mixedSectorSymbol_sq_le {q : Parameters} (hq : q.Admissible)
    (p : Fin 2 → ℝ) (s u : ℝ) :
    ‖mixedSectorSymbol q p s u‖ ^ 2 ≤
      2 * ‖mixedRawResidual q |p 0| (p 1) (p 1 + s) (p 0 + u)‖ ^ 2 +
        2 * ‖projectionMixedError (rawDiagonalPart (p 1)
          (periodizeRow (correctionCoefficient 40 q |p 0| (p 1)))) (p 0 + u)‖ ^ 2 := by
  have hsig : ‖((Real.sign (Real.sin (p 0)) : ℝ) : ℂ)‖ ≤ 1 := by
    rcases Real.sign_apply_eq (Real.sin (p 0)) with h | h | h <;> simp [h]
  set X : ℂ := mixedRawResidual q |p 0| (p 1) (p 1 + s) (p 0 + u) with hX
  set Y : ℂ := projectionMixedError (rawDiagonalPart (p 1)
    (periodizeRow (correctionCoefficient 40 q |p 0| (p 1)))) (p 0 + u) with hY
  have hnorm : ‖mixedSectorSymbol q p s u‖ ≤ ‖X‖ + ‖Y‖ := by
    rw [mixedSectorSymbol_eq hq p s u, norm_mul]
    calc ‖((Real.sign (Real.sin (p 0)) : ℝ) : ℂ)‖ * ‖X + Y‖ ≤ 1 * ‖X + Y‖ :=
          mul_le_mul_of_nonneg_right hsig (norm_nonneg _)
      _ = ‖X + Y‖ := one_mul _
      _ ≤ ‖X‖ + ‖Y‖ := norm_add_le _ _
  nlinarith [norm_nonneg (mixedSectorSymbol q p s u), norm_nonneg X, norm_nonneg Y,
    sq_nonneg (‖X‖ - ‖Y‖)]

/-- Pointwise domination of iterated normalized torus integrals. -/
theorem torusIntegral₂_le_of_pointwise {S A B : ℝ → ℝ → ℝ}
    (hmA : Measurable fun z : ℝ × ℝ => A z.1 z.2)
    (hmB : Measurable fun z : ℝ × ℝ => B z.1 z.2)
    {CA CB : ℝ} (hbA : ∀ s u, |A s u| ≤ CA) (hbB : ∀ s u, |B s u| ≤ CB)
    (hnnS : ∀ s u, 0 ≤ S s u)
    (hpt : ∀ s u, S s u ≤ 2 * A s u + 2 * B s u) :
    (Estimates.torusIntegral fun s => Estimates.torusIntegral fun u => S s u) ≤
      2 * (Estimates.torusIntegral fun s => Estimates.torusIntegral fun u => A s u) +
        2 * (Estimates.torusIntegral fun s => Estimates.torusIntegral fun u => B s u) := by
  have hmA' : ∀ s : ℝ, Measurable fun u => A s u := fun s =>
    hmA.comp (measurable_const.prodMk measurable_id)
  have hmB' : ∀ s : ℝ, Measurable fun u => B s u := fun s =>
    hmB.comp (measurable_const.prodMk measurable_id)
  have hintA : ∀ s : ℝ, Integrable (fun u => 2 * A s u)
      (volume.restrict Estimates.torus) := fun s =>
    integrable_torus_of_bound ((hmA' s).const_mul 2).aestronglyMeasurable
      (C := 2 * CA) (fun u => by
        rw [Real.norm_eq_abs, abs_mul, abs_two]
        nlinarith [hbA s u])
  have hintB : ∀ s : ℝ, Integrable (fun u => 2 * B s u)
      (volume.restrict Estimates.torus) := fun s =>
    integrable_torus_of_bound ((hmB' s).const_mul 2).aestronglyMeasurable
      (C := 2 * CB) (fun u => by
        rw [Real.norm_eq_abs, abs_mul, abs_two]
        nlinarith [hbB s u])
  have hinner : ∀ s : ℝ,
      (Estimates.torusIntegral fun u => S s u) ≤
        2 * (Estimates.torusIntegral fun u => A s u) +
          2 * (Estimates.torusIntegral fun u => B s u) := by
    intro s
    calc (Estimates.torusIntegral fun u => S s u)
        ≤ Estimates.torusIntegral (fun u => 2 * A s u + 2 * B s u) :=
          torusIntegral_mono' (fun u => hnnS s u) ((hintA s).add (hintB s))
            (fun u => hpt s u)
      _ = 2 * (Estimates.torusIntegral fun u => A s u) +
            2 * (Estimates.torusIntegral fun u => B s u) := by
          rw [torusIntegral_add (hintA s) (hintB s), torusIntegral_smul_left,
            torusIntegral_smul_left]
  have hmeasA : Measurable fun s : ℝ => Estimates.torusIntegral fun u => A s u :=
    (stronglyMeasurable_torusIntegral (F := fun w : ℝ × ℝ => A w.1 w.2)
      hmA.stronglyMeasurable).measurable
  have hmeasB : Measurable fun s : ℝ => Estimates.torusIntegral fun u => B s u :=
    (stronglyMeasurable_torusIntegral (F := fun w : ℝ × ℝ => B w.1 w.2)
      hmB.stronglyMeasurable).measurable
  have hIA : ∀ s : ℝ, |Estimates.torusIntegral fun u => A s u| ≤ CA := fun s => by
    simpa [Real.norm_eq_abs] using
      norm_torusIntegral_le_of_bound (f := fun u => A s u)
        (fun u => by simpa [Real.norm_eq_abs] using hbA s u)
  have hIB : ∀ s : ℝ, |Estimates.torusIntegral fun u => B s u| ≤ CB := fun s => by
    simpa [Real.norm_eq_abs] using
      norm_torusIntegral_le_of_bound (f := fun u => B s u)
        (fun u => by simpa [Real.norm_eq_abs] using hbB s u)
  have hoA : Integrable (fun s => 2 * (Estimates.torusIntegral fun u => A s u))
      (volume.restrict Estimates.torus) :=
    integrable_torus_of_bound (hmeasA.const_mul 2).aestronglyMeasurable
      (C := 2 * CA) (fun s => by
        rw [Real.norm_eq_abs, abs_mul, abs_two]
        nlinarith [hIA s])
  have hoB : Integrable (fun s => 2 * (Estimates.torusIntegral fun u => B s u))
      (volume.restrict Estimates.torus) :=
    integrable_torus_of_bound (hmeasB.const_mul 2).aestronglyMeasurable
      (C := 2 * CB) (fun s => by
        rw [Real.norm_eq_abs, abs_mul, abs_two]
        nlinarith [hIB s])
  calc (Estimates.torusIntegral fun s => Estimates.torusIntegral fun u => S s u)
      ≤ Estimates.torusIntegral (fun s =>
          2 * (Estimates.torusIntegral fun u => A s u) +
            2 * (Estimates.torusIntegral fun u => B s u)) :=
        torusIntegral_mono' (fun s => torusIntegral_nonneg' (fun u => hnnS s u))
          (hoA.add hoB) hinner
    _ = _ := by
        rw [torusIntegral_add hoA hoB, torusIntegral_smul_left, torusIntegral_smul_left]


theorem measurable_mixedHMinusWeight_shift (q : Parameters) (c1 c2 : ℝ) :
    Measurable fun z : ℝ × ℝ => mixedHMinusWeight q (c1 + z.1) (c2 + z.2) := by
  unfold mixedHMinusWeight Estimates.dispersion
  fun_prop

theorem measurable_weight_norm_sq_shift {F : ℝ → ℝ → ℂ}
    (hF : Measurable fun z : ℝ × ℝ => F z.1 z.2) (q : Parameters) (c1 c2 : ℝ) :
    Measurable fun z : ℝ × ℝ =>
      mixedHMinusWeight q (c1 + z.1) (c2 + z.2) * ‖F (c1 + z.1) (c2 + z.2)‖ ^ 2 := by
  have hshift : Measurable fun z : ℝ × ℝ => ((c1 + z.1, c2 + z.2) : ℝ × ℝ) :=
    (measurable_const.add measurable_fst).prodMk (measurable_const.add measurable_snd)
  exact (measurable_mixedHMinusWeight_shift q c1 c2).mul
    ((hF.comp hshift).norm.pow_const 2)

/-- **The mixed sector energy is dominated by the scalar residual energy and
the coincident-row energy.** -/
theorem mixedSector_energy_le {q : Parameters} (hq : q.Admissible) {p : Fin 2 → ℝ}
    (hp₂ : |p 1| ≤ |p 0|)
    (hw1 : 2 * q.rho + |p 1| < Real.pi) (hw2 : q.rho + |p 0| < Real.pi) :
    (Estimates.torusIntegral fun s => Estimates.torusIntegral fun u =>
        mixedHMinusWeight q (p 1 + s) (p 0 + u) *
          ‖mixedSectorSymbol q p s u‖ ^ 2) ≤
      2 * mixedRawResidualHMinusSq q |p 0| (p 1) +
        2 * projectionErrorHMinusSq q (rawDiagonalPart (p 1)
          (periodizeRow (correctionCoefficient 40 q |p 0| (p 1)))) := by
  classical
  have hlam := hq.1
  have ha : (0 : ℝ) ≤ |p 0| := abs_nonneg _
  obtain ⟨hmM, CM, hCM⟩ := torusBounded₂_mixedRawResidual hq |p 0| (p 1)
  obtain ⟨hmD, CD, hCD⟩ := torusBounded₁_projectionMixedError
    ((torusBounded₃_periodizeRow
      (torusBounded₃_correctionCoefficient (by norm_num : (0:ℝ) < 40) hlam |p 0|
        (p 1))).rawDiagonalPart (p 1))
  have hmA : Measurable fun z : ℝ × ℝ =>
      mixedHMinusWeight q (p 1 + z.1) (p 0 + z.2) *
        ‖mixedRawResidual q |p 0| (p 1) (p 1 + z.1) (p 0 + z.2)‖ ^ 2 :=
    measurable_weight_norm_sq_shift hmM q (p 1) (p 0)
  have hmB : Measurable fun z : ℝ × ℝ =>
      mixedHMinusWeight q (p 1 + z.1) (p 0 + z.2) *
        ‖projectionMixedError (rawDiagonalPart (p 1)
          (periodizeRow (correctionCoefficient 40 q |p 0| (p 1)))) (p 0 + z.2)‖ ^ 2 :=
    measurable_weight_norm_sq_shift (F := fun _ beta =>
      projectionMixedError (rawDiagonalPart (p 1)
        (periodizeRow (correctionCoefficient 40 q |p 0| (p 1)))) beta)
      (hmD.comp measurable_snd) q (p 1) (p 0)
  have hbA : ∀ s u : ℝ, |mixedHMinusWeight q (p 1 + s) (p 0 + u) *
      ‖mixedRawResidual q |p 0| (p 1) (p 1 + s) (p 0 + u)‖ ^ 2| ≤
      q.lambda⁻¹ * CM ^ 2 := fun s u =>
    abs_weight_norm_sq_le (F := mixedRawResidual q |p 0| (p 1)) hlam hCM _ _
  have hbB : ∀ s u : ℝ, |mixedHMinusWeight q (p 1 + s) (p 0 + u) *
      ‖projectionMixedError (rawDiagonalPart (p 1)
        (periodizeRow (correctionCoefficient 40 q |p 0| (p 1)))) (p 0 + u)‖ ^ 2| ≤
      q.lambda⁻¹ * CD ^ 2 := fun s u =>
    abs_weight_norm_sq_le (F := fun _ b => projectionMixedError
      (rawDiagonalPart (p 1) (periodizeRow (correctionCoefficient 40 q |p 0| (p 1)))) b)
      hlam (fun _ b => hCD b) _ _
  have hnnS : ∀ s u : ℝ, 0 ≤ mixedHMinusWeight q (p 1 + s) (p 0 + u) *
      ‖mixedSectorSymbol q p s u‖ ^ 2 := fun s u =>
    mul_nonneg (mixedHMinusWeight_pos hlam _ _).le (sq_nonneg _)
  have hpt : ∀ s u : ℝ, mixedHMinusWeight q (p 1 + s) (p 0 + u) *
      ‖mixedSectorSymbol q p s u‖ ^ 2 ≤
      2 * (mixedHMinusWeight q (p 1 + s) (p 0 + u) *
          ‖mixedRawResidual q |p 0| (p 1) (p 1 + s) (p 0 + u)‖ ^ 2) +
        2 * (mixedHMinusWeight q (p 1 + s) (p 0 + u) *
          ‖projectionMixedError (rawDiagonalPart (p 1)
            (periodizeRow (correctionCoefficient 40 q |p 0| (p 1)))) (p 0 + u)‖ ^ 2) := by
    intro s u
    have hw := (mixedHMinusWeight_pos hlam (p 1 + s) (p 0 + u)).le
    have h := norm_mixedSectorSymbol_sq_le hq p s u
    nlinarith [h, hw]
  rw [← mixedRawResidual_energy_translate hq ha hp₂ hw1 hw2,
    ← projectionError_energy_translate (p₂ := p 1) hq ha hw2]
  exact torusIntegral₂_le_of_pointwise hmA hmB hbA hbB hnnS hpt

end

end Manhattan.Glue
