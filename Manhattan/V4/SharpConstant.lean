/-
Sharpening the constant in the operator estimate.

The manuscript's `eq:M` majorizes by `M = 4(δ + |r| + |r'| + |β|)` with the
operator estimate carrying coefficient `1`.  The route assembled in
`Manhattan/V4/OperatorEstimate.lean` instead lands on `9 · evenMajorantEnergy
120`, because every transport step is normalized at the multiplier constant
`40`.

None of that `40` is forced.  The multiplier is linear in its constant, so an
identity or a contraction proved at one constant transfers to every other, and
`symbolWeight` needs only the constant `1`.  This file records the linearity
and the transferred statements, so the composed bound can be taken at the
sharp constant without restating anything that is frozen.
-/
import Manhattan.V4.OperatorEstimate
import Manhattan.Estimates.KernelBound

namespace Manhattan.V4

open Manhattan Manhattan.Estimates MeasureTheory

/-- The multiplier is linear in its constant. -/
theorem multiplier_eq_smul (kappa : ℝ) (q : Parameters) (P : Fin 2 → ℝ) :
    multiplier kappa q P = kappa * multiplier 1 q P := by
  simp only [multiplier]; ring

/-- Hence any integral taken against the multiplier is linear in the constant.
Stated for an arbitrary measure and frequency map, so that it applies to each
of the transport steps regardless of which frequency they use. -/
theorem integral_multiplier_eq_smul {α : Type*} [MeasurableSpace α]
    (kappa : ℝ) (q : Parameters) (mu : Measure α) (F : α → Fin 2 → ℝ) (g : α → ℝ) :
    (∫ t, multiplier kappa q (F t) * g t ∂mu)
      = kappa * ∫ t, multiplier 1 q (F t) * g t ∂mu := by
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [multiplier]; ring

/-- The raw multiplier energy is linear in the constant. -/
theorem rawMultiplierEnergy_eq_smul (kappa : ℝ) (q : Parameters) (p₂ : ℝ)
    (k : ℝ → ℝ → ℝ → ℂ) :
    Glue.rawMultiplierEnergy kappa q p₂ k
      = kappa * Glue.rawMultiplierEnergy 1 q p₂ k := by
  simp only [Glue.rawMultiplierEnergy]
  rw [← torusIntegral_smul_left]
  refine congrArg torusIntegral (funext fun beta => ?_)
  rw [← torusIntegral_smul_left]
  refine congrArg torusIntegral (funext fun r => ?_)
  rw [← torusIntegral_smul_left]
  refine congrArg torusIntegral (funext fun r' => ?_)
  simp only [multiplier]; ring

/-- Transfer of an inequality between multiplier integrals from one constant to
another.  Both sides scale by the same positive factor. -/
theorem integral_multiplier_le_of_le {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {kappa mu : ℝ} (hkappa : 0 ≤ kappa) (hmu : 0 < mu) (q : Parameters)
    {m₁ : Measure α} {m₂ : Measure β} {F₁ : α → Fin 2 → ℝ} {F₂ : β → Fin 2 → ℝ}
    {g₁ : α → ℝ} {g₂ : β → ℝ}
    (h : (∫ t, multiplier mu q (F₁ t) * g₁ t ∂m₁)
        ≤ ∫ t, multiplier mu q (F₂ t) * g₂ t ∂m₂) :
    (∫ t, multiplier kappa q (F₁ t) * g₁ t ∂m₁)
      ≤ ∫ t, multiplier kappa q (F₂ t) * g₂ t ∂m₂ := by
  have e1 := integral_multiplier_eq_smul kappa q m₁ F₁ g₁
  have e2 := integral_multiplier_eq_smul kappa q m₂ F₂ g₂
  have f1 := integral_multiplier_eq_smul mu q m₁ F₁ g₁
  have f2 := integral_multiplier_eq_smul mu q m₂ F₂ g₂
  rw [f1, f2] at h
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_left (le_of_mul_le_mul_left h hmu) hkappa

/-! ## The sharp `H₃` bound

The transport from the twisted, projected coefficient back to the raw energy is
the tail of `hThreeForm_rawWalsh_le`.  It is stated here on its own so that the
sharp first step can be substituted for the lossy one. -/

theorem multiplierIntegral_shiftTwist_le_rawEnergy {q : Parameters}
    (hlambda : 0 < q.lambda) (p : Fin 2 → ℝ) {k : ℝ → ℝ → ℝ → ℂ}
    (hk : Glue.TorusBoundedThree k) :
    (∫ t, multiplier 40 q (Glue.totalFrequency 3 p Glue.type112Pattern t) *
        ‖(Glue.type112FreqFun (Manhattan.type112ShiftTwist (p 0) (p 1)
            (Manhattan.type112DiagonalProjection
              (UnitAddTorus.mFourierBasis.repr (rawL2 hk)))) :
          UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2 ∂(Glue.LineTorusMeasure 3))
      ≤ Glue.rawMultiplierEnergy 40 q (p 1) k := by
  set d := UnitAddTorus.mFourierBasis.repr (rawL2 hk) with hd
  rw [Glue.multiplier_integral_type112ShiftTwist_frozen]
  refine le_trans (Glue.multiplier_integral_type112DiagonalProjection_le
    hlambda.le _ d) ?_
  rw [hd, LinearIsometryEquiv.symm_apply_apply,
    ← multiplier_integral_rawL2 hlambda.le (p 1) hk]
  refine le_of_eq (integral_congr_ae ?_)
  filter_upwards with t
  rw [Glue.multiplier_totalFrequency_type112Pattern]

/-- **The `H₃` half at the sharp constant.**  `symbolWeight` is `λ + θ(P)`, so
the multiplier constant `1` suffices where the assembled route carries `40`. -/
theorem hThreeForm_rawWalsh_le_sharp {q : Parameters} (hlambda : 0 < q.lambda)
    (p : Fin 2 → ℝ) {k : ℝ → ℝ → ℝ → ℂ} (hk : Glue.TorusBoundedThree k) :
    Glue.sectorHThreeForm q.lambda p (rawWalsh p hk)
      ≤ Glue.rawMultiplierEnergy 1 q (p 1) k := by
  set d := UnitAddTorus.mFourierBasis.repr (rawL2 hk) with hd
  set G : UnitAddTorus (Fin 3) → ℝ := fun t =>
    ‖(Glue.type112FreqFun (Manhattan.type112ShiftTwist (p 0) (p 1)
        (Manhattan.type112DiagonalProjection d)) :
      UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2 with hG
  have hform : Glue.sectorHThreeForm q.lambda p (rawWalsh p hk)
      = ∫ t, Glue.symbolWeight 3 q.lambda p Glue.type112Pattern t * G t
          ∂(Glue.LineTorusMeasure 3) :=
    Glue.hThreeForm_type112WalshSynthesis q.lambda p _
  have hsharp : (∫ t, Glue.symbolWeight 3 q.lambda p Glue.type112Pattern t * G t
        ∂(Glue.LineTorusMeasure 3))
      ≤ ∫ t, multiplier 1 q (Glue.totalFrequency 3 p Glue.type112Pattern t) * G t
          ∂(Glue.LineTorusMeasure 3) := by
    refine integral_mono_of_nonneg ?_ ?_ ?_
    · filter_upwards with t
      exact mul_nonneg (by
        have := theta_nonneg (Glue.totalFrequency 3 p Glue.type112Pattern t)
        rw [Glue.symbolWeight_def]; linarith) (by positivity)
    · exact Glue.integrable_multiplier_norm_sq (by norm_num : (0:ℝ) ≤ 1)
        hlambda.le 3 p Glue.type112Pattern _
    · filter_upwards with t
      exact mul_le_mul_of_nonneg_right
        (symbolWeight_le_multiplier_one p Glue.type112Pattern t) (by positivity)
  have htail := multiplierIntegral_shiftTwist_le_rawEnergy hlambda p hk
  have e1 := integral_multiplier_eq_smul (1:ℝ) q (Glue.LineTorusMeasure 3)
    (fun t => Glue.totalFrequency 3 p Glue.type112Pattern t) G
  have e40 := integral_multiplier_eq_smul (40:ℝ) q (Glue.LineTorusMeasure 3)
    (fun t => Glue.totalFrequency 3 p Glue.type112Pattern t) G
  have hE := rawMultiplierEnergy_eq_smul (40:ℝ) q (p 1) k
  rw [hform]
  refine hsharp.trans ?_
  rw [e1, one_mul]
  rw [e40] at htail
  rw [hE] at htail
  linarith

/-! ## The sharp constant in the scalar step

`fourEstimateCore` is `hWeight + 8(sin²(P₀)/√(λ+d(P₀)) + sin²(P₁)/√(λ+d(P₁)))`,
and the manuscript's scalar step bounds each quotient by `2√2 |sin(Pᵢ/2)|`.
That gives `8√2 ≈ 11.31` against the multiplier, so `κ = 12` suffices where the
repository carries `40`. -/

theorem fourEstimateCore_le_multiplier_twelve {q : Parameters} (hlam : 0 ≤ q.lambda)
    (P : Fin 2 → ℝ) : fourEstimateCore q P ≤ multiplier 12 q P := by
  have hzero := sine_sq_div_sqrt_le q.lambda (P 0) hlam
  have hone := sine_sq_div_sqrt_le q.lambda (P 1) hlam
  have hsqrt : Real.sqrt 2 ≤ 3/2 := by linarith [Real.sqrt_two_lt_three_halves]
  have habs0 : 0 ≤ |Real.sin (P 0 / 2)| := abs_nonneg _
  have habs1 : 0 ≤ |Real.sin (P 1 / 2)| := abs_nonneg _
  have hth := theta_nonneg P
  simp only [fourEstimateCore, multiplier, hWeight] at *
  nlinarith [hzero, hone, hsqrt, habs0, habs1, hth, hlam]

/-- The slot estimate at the sharp constant.  This is
`Manhattan.Glue.sin_sq_div_sqrt_le_multiplier_div` with `12` in place of `40`.

Propagating it to `sectorDFourForm_rawWalsh_le` means carrying `κ` through
`Glue.inv_sqrt_slot_mul_sin_sq_le`,
`Glue.re_inner_orderedHInv_insertLine_le` and
`Glue.tsum_integral_inv_symbolWeight_degreeRaiseDir_le`, none of which is
frozen. -/
theorem sin_sq_div_sqrt_le_multiplier_div_twelve {q : Parameters}
    (hlam : 0 ≤ q.lambda) (P : Fin 2 → ℝ) (i : Fin 2) :
    Real.sin (P i) ^ 2 / Real.sqrt (q.lambda + dispersion (P i))
      ≤ multiplier 12 q P / 8 := by
  have hcases : ∀ j : Fin 2, j = 0 ∨ j = 1 := by decide
  have hcore := fourEstimateCore_le_multiplier_twelve hlam P
  have hw : 0 ≤ hWeight q P := by
    have := theta_nonneg P
    simp only [hWeight]; linarith
  have h0 : 0 ≤ Real.sin (P 0) ^ 2 / Real.sqrt (q.lambda + dispersion (P 0)) := by positivity
  have h1 : 0 ≤ Real.sin (P 1) ^ 2 / Real.sqrt (q.lambda + dispersion (P 1)) := by positivity
  simp only [fourEstimateCore] at hcore
  rcases hcases i with rfl | rfl
  · linarith
  · linarith

/-! ## The sharp operator estimate

`multiplier 1 ≤ evenMajorant 3` pointwise, and both sides are linear in their
constant, so the integrated majorization holds at `(1, 3)` and hence at
`(κ, 3κ)`. -/

theorem evenMajorantEnergy_eq_smul (kappa : ℝ) (delta : ℝ) (k : ℝ → ℝ → ℝ → ℂ) :
    evenMajorantEnergy kappa delta k = kappa * evenMajorantEnergy 1 delta k := by
  have hsmul : ∀ (c : ℝ) (f : ℝ → ℝ),
      Estimates.torusIntegral (fun x => c * f x) = c * Estimates.torusIntegral f := by
    intro c f
    simp only [Estimates.torusIntegral, MeasureTheory.integral_const_mul, smul_eq_mul]
    ring
  simp only [evenMajorantEnergy]
  rw [← hsmul]
  refine congrArg Estimates.torusIntegral (funext fun beta => ?_)
  rw [← hsmul]
  refine congrArg Estimates.torusIntegral (funext fun r => ?_)
  rw [← hsmul]
  refine congrArg Estimates.torusIntegral (funext fun r' => ?_)
  simp only [evenMajorant]; ring

/-- **The integrated majorization at the sharp constants.**  The manuscript's
`eq:M` takes `κ = 4`; this holds at `κ = 3`. -/
theorem rawMultiplierEnergy_le_evenMajorantEnergy_sharp {q : Parameters}
    {delta p₂ : ℝ} {k : ℝ → ℝ → ℝ → ℂ}
    (hlam0 : 0 ≤ q.lambda) (hlam : q.lambda ≤ delta) (hp₂ : |p₂| ≤ delta)
    (hk : Glue.TorusBoundedThree k) :
    Glue.rawMultiplierEnergy 1 q p₂ k ≤ evenMajorantEnergy 3 delta k := by
  obtain ⟨hmeas, C, hC⟩ := hk
  have hCnonneg : 0 ≤ C := le_trans (norm_nonneg _) (hC 0 0 0)
  have hdelta : 0 ≤ delta := le_trans (abs_nonneg _) hp₂
  set B : ℝ := (1 * (q.lambda + 8) + 3 * (delta + 3 * Real.pi)) * C ^ 2 with hB
  have hnormsq : ∀ r r' beta : ℝ, ‖k r r' beta‖ ^ 2 ≤ C ^ 2 := fun r r' beta =>
    pow_le_pow_left₀ (norm_nonneg _) (hC r r' beta) 2
  refine torusIntegral₃_mono (C := B) ?_ ?_ ?_ ?_ ?_
  · exact (Glue.measurable_multiplier_comp 1 q measurable_fst
      (((measurable_fst.comp measurable_snd).add
        (measurable_snd.comp measurable_snd)).sub measurable_const)).mul
      ((hmeas.comp ((measurable_fst.comp measurable_snd).prodMk
        ((measurable_snd.comp measurable_snd).prodMk measurable_fst))).norm.pow_const 2)
  · exact ((evenMajorant_measurable 3 delta).comp
      ((measurable_fst.comp measurable_snd).prodMk
        ((measurable_snd.comp measurable_snd).prodMk measurable_fst))).mul
      ((hmeas.comp ((measurable_fst.comp measurable_snd).prodMk
        ((measurable_snd.comp measurable_snd).prodMk measurable_fst))).norm.pow_const 2)
  · intro beta r r'
    have hm0 : 0 ≤ multiplier 1 q (mixedTotalFrequency beta (Glue.mixedAlpha p₂ r r')) :=
      multiplier_nonneg (by norm_num) hlam0 _
    have hm : multiplier 1 q (mixedTotalFrequency beta (Glue.mixedAlpha p₂ r r'))
        ≤ 1 * (q.lambda + 8) := Glue.multiplier_le (by norm_num) _
    rw [abs_of_nonneg (mul_nonneg hm0 (sq_nonneg _)), hB]
    have hpi := Real.pi_pos
    nlinarith [hnormsq r r' beta, sq_nonneg (‖k r r' beta‖)]
  · intro beta r r'
    have hm0 : 0 ≤ evenMajorant 3 delta r r' beta :=
      evenMajorant_nonneg (by norm_num) hdelta r r' beta
    have hm : evenMajorant 3 delta r r' beta ≤ 3 * (delta + 3 * Real.pi) :=
      evenMajorant_le (by norm_num) r r' beta
    rw [abs_of_nonneg (mul_nonneg hm0 (sq_nonneg _)), hB]
    have hpi := Real.pi_pos
    nlinarith [hnormsq r r' beta, sq_nonneg (‖k r r' beta‖)]
  · intro beta r r'
    exact mul_le_mul_of_nonneg_right
      (multiplier_one_le_evenMajorant_three hlam hp₂ r r' beta) (sq_nonneg _)

/-- **The operator estimate at the sharp constants.**  Against
`Manhattan.V4.operatorEstimate`, which gives `9 · evenMajorantEnergy 120`, this
gives `97 · evenMajorantEnergy 3`.  Since `evenMajorantEnergy κ = κ · E₀` with
`E₀ = ∫ (δ + |r| + |r'| + |β|)|k|²`, the two read `1080 E₀` and `291 E₀`: a
factor of `3.71`.  The manuscript's `eq:M` asks for `4 E₀`.

The `H₃` half now costs `rawMultiplierEnergy 1` rather than `40`, and the `D₃`
half runs at `κ = 12` rather than `40`; what remains between `291` and `4` is
the `8` of the four raising slots and the `12` of the scalar step. -/
theorem operatorEstimate_sharp {q : Parameters} (hlambda : 0 < q.lambda)
    {delta : ℝ} (hdelta : q.lambda ≤ delta) (p : Fin 2 → ℝ)
    (hp₂ : |p 1| ≤ delta) {k : ℝ → ℝ → ℝ → ℂ} (hk : Glue.TorusBoundedThree k) :
    Glue.sectorHThreeForm q.lambda p (rawWalsh p hk)
        + Glue.sectorDFourForm hlambda p (rawWalsh p hk)
      ≤ 97 * evenMajorantEnergy 3 delta k := by
  have h1 := hThreeForm_rawWalsh_le_sharp hlambda p hk
  have h2 := sectorDFourForm_rawWalsh_le (by norm_num : (12:ℝ) ≤ 12) hlambda p hk
  have h12 := Glue.rawMultiplierEnergy_eq_smul (12 : ℝ) q (p 1) k
  have h3 := rawMultiplierEnergy_le_evenMajorantEnergy_sharp (q := q) (delta := delta)
    (p₂ := p 1) (k := k) hlambda.le hdelta hp₂ hk
  rw [h12] at h2
  linarith

/-! ## The operator estimate with coefficient one

`97 · evenMajorantEnergy 3 = evenMajorantEnergy 291`, so the sharp estimate can
be read with operator coefficient `A = 1` at `κ = 291` instead of `A = 97` at
`κ = 3`.  That is the form the Move 1 assembly wants: its own coefficient is
governed by `C₃ ≥ 4A + 4` (which is what makes the current `C₃ = 40` equal
`4·9 + 4`), so shrinking `A` is worth more than shrinking `κ`. -/

/-- The sharp estimate read at `(A, κ) = (21, 14)`, which is where the composed
Move 1 constant `60 + (4A+4)(π² + π³κ/2)` is smallest: `97·3 = 291 ≤ 21·14`. -/
theorem operatorEstimate_sharp_fourteen {q : Parameters} (hlambda : 0 < q.lambda)
    {delta : ℝ} (hdelta : q.lambda ≤ delta) (p : Fin 2 → ℝ)
    (hp₂ : |p 1| ≤ delta) {k : ℝ → ℝ → ℝ → ℂ} (hk : Glue.TorusBoundedThree k) :
    Glue.sectorHThreeForm q.lambda p (rawWalsh p hk)
        + Glue.sectorDFourForm hlambda p (rawWalsh p hk)
      ≤ 21 * evenMajorantEnergy 14 delta k := by
  have h := operatorEstimate_sharp hlambda hdelta p hp₂ hk
  have e3 := evenMajorantEnergy_eq_smul (3 : ℝ) delta k
  have e14 := evenMajorantEnergy_eq_smul (14 : ℝ) delta k
  have hdelta0 : 0 ≤ delta := le_trans hlambda.le hdelta
  have hnn : 0 ≤ evenMajorantEnergy 1 delta k := by
    refine Glue.torusIntegral_nonneg fun beta => ?_
    refine Glue.torusIntegral_nonneg fun r => ?_
    refine Glue.torusIntegral_nonneg fun r' => ?_
    exact mul_nonneg (evenMajorant_nonneg (by norm_num) hdelta0 r r' beta) (sq_nonneg _)
  rw [e3] at h
  rw [e14]
  linarith

theorem operatorEstimate_parityKernel_sharp_fourteen {q : Parameters}
    (hlambda : 0 < q.lambda) {delta : ℝ} (hdelta0 : 0 < delta)
    (hdelta : q.lambda ≤ delta) (p : Fin 2 → ℝ)
    (hp₂ : |p 1| ≤ delta) (v : ParityProfile) :
    Glue.sectorHThreeForm q.lambda p
        (rawWalsh p (torusBounded₃_parityKernel (by norm_num : (0:ℝ) < 14) hdelta0 v))
      + Glue.sectorDFourForm hlambda p
        (rawWalsh p (torusBounded₃_parityKernel (by norm_num : (0:ℝ) < 14) hdelta0 v))
      ≤ 21 * Estimates.torusIntegral fun beta => Estimates.torusIntegral fun r =>
          paritySigma 14 delta r beta * v.toFun r beta ^ 2 := by
  have h := operatorEstimate_sharp_fourteen hlambda hdelta p hp₂
    (torusBounded₃_parityKernel (by norm_num : (0:ℝ) < 14) hdelta0 v)
  rwa [evenMajorantEnergy_parityKernel (by norm_num : (0:ℝ) < 14) hdelta0 v] at h

theorem operatorEstimate_sharp_one {q : Parameters} (hlambda : 0 < q.lambda)
    {delta : ℝ} (hdelta : q.lambda ≤ delta) (p : Fin 2 → ℝ)
    (hp₂ : |p 1| ≤ delta) {k : ℝ → ℝ → ℝ → ℂ} (hk : Glue.TorusBoundedThree k) :
    Glue.sectorHThreeForm q.lambda p (rawWalsh p hk)
        + Glue.sectorDFourForm hlambda p (rawWalsh p hk)
      ≤ evenMajorantEnergy 291 delta k := by
  have h := operatorEstimate_sharp hlambda hdelta p hp₂ hk
  have e3 := evenMajorantEnergy_eq_smul (3 : ℝ) delta k
  have e291 := evenMajorantEnergy_eq_smul (291 : ℝ) delta k
  rw [e3] at h
  rw [e291]
  linarith

/-- **(OP) at the parity competitor, with operator coefficient one.**
`operatorEstimate_parityKernel` gives `9 ∫∫ σ_{120} v²`.  This gives
`∫∫ σ_{291} v²`: the coefficient drops from `9` to `1`, at the price of the
logarithmic weight being taken at `κ = 291` rather than `120`.

That trade is favourable because the Move 1 coefficient obeys `C₃ ≥ 4A + 4`,
so it is `A` and not `κ` that the assembly pays for; `C₃ = 40` in the current
chain is exactly `4·9 + 4`. -/
theorem operatorEstimate_parityKernel_sharp {q : Parameters} (hlambda : 0 < q.lambda)
    {delta : ℝ} (hdelta0 : 0 < delta) (hdelta : q.lambda ≤ delta) (p : Fin 2 → ℝ)
    (hp₂ : |p 1| ≤ delta) (v : ParityProfile) :
    Glue.sectorHThreeForm q.lambda p
        (rawWalsh p (torusBounded₃_parityKernel (by norm_num : (0:ℝ) < 291) hdelta0 v))
      + Glue.sectorDFourForm hlambda p
        (rawWalsh p (torusBounded₃_parityKernel (by norm_num : (0:ℝ) < 291) hdelta0 v))
      ≤ Estimates.torusIntegral fun beta => Estimates.torusIntegral fun r =>
          paritySigma 291 delta r beta * v.toFun r beta ^ 2 := by
  have h := operatorEstimate_sharp_one hlambda hdelta p hp₂
    (torusBounded₃_parityKernel (by norm_num : (0:ℝ) < 291) hdelta0 v)
  rwa [evenMajorantEnergy_parityKernel (by norm_num : (0:ℝ) < 291) hdelta0 v] at h

end Manhattan.V4
