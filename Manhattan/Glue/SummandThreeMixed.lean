import Manhattan.Glue.CorrectionLowering

/-!
# The mixed degree-two sector of summand 3: the sign of the correction

The mixed `(h,v)` half of summand 3 of (22) is the `H⁻¹` energy of

  `(D₁f_p)₁₂ - (D₂*k_p)₁₂`,

whose Walsh coefficients are computed by
`Manhattan.Glue.type12WalshAnalysis_sub_type112DStarMixed_apply` (the raising
half) and `Manhattan.Glue.mixedFourierCoefficient_correction` (the lowering
half).  Transporting that vector to the frequency side with
`Manhattan.Glue.type12FreqFun_eq_of_mFourierCoeff` and
`Manhattan.Glue.hMinusEnergy_type12WalshSynthesis_torusIntegral` turns the
sector energy into the scalar integral bounded by
`Manhattan.Glue.mixedRawResidualHMinusSq_le_sqrtScale`, **provided** the
frequency function of the sector is the scalar residual
`Manhattan.Glue.mixedRawResidual`.

This file records the scalar half of that identification, and in particular
the one place where the two sides do not line up.  The raising half of the
mixed sector is the paper's `w(r,β) = i sin(r) f_p(r)`, which is
`Manhattan.Estimates.mixedResidual` and hence, by
`Manhattan.Estimates.mixedResidual_eq_indicator`, the **signed** indicator
`sgn(sin p₁)1_I(r)`.  The scalar residual `Manhattan.Glue.mixedRawResidual`
subtracts `D̃₂*k̃` from the **unsigned** indicator
`Manhattan.Glue.rawMixedTarget`.  The manuscript reconciles the two by
multiplying the coefficient of Proposition 4.2 by `sgn(sin p₁)` before calling
it `k_p` (`manuscript.tex:1138-1141`).

`Manhattan.Glue.mixedResidual_sub_signedCorrection` below is that
reconciliation: with the `sgn(sin p₁)` multiplier in place, the mixed residual
of the competitor is `sgn(sin p₁)` times `mixedRawResidual`, so
`Manhattan.Glue.signedMixedResidualHMinusSq_le_sqrtScale` gives the mixed
scalar energy the bound `C√L` of Lemma 5.4.

`Manhattan.Glue.mixedResidual_sub_correction_of_sin_neg` and
`Manhattan.Glue.norm_mixedResidual_le_norm_sub_correction_of_sin_neg` record
what happens without the multiplier: for `sin p₁ < 0` the two terms add
instead of cancelling, and the residual is pointwise at least as large as the
uncorrected mixed residual of Lemma 4.1(c).

Paper: `lem:onecoin` = Lemma 4.1 (`manuscript.tex:907-958`), `prop:key` =
Proposition 4.2 (`manuscript.tex:1007`), `lem:correction-calculation` =
Lemma 5.4 (`manuscript.tex:1305`), and the `sgn(sin p₁)` prescription at
`manuscript.tex:1138-1141`.
-/

open MeasureTheory Set

namespace Manhattan.Glue

noncomputable section

open Manhattan.Estimates

local instance summandThreeMixedPropDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-! ## The scalar mixed target of `D₁f_p` carries the sign of `sin p₁` -/

/-- The signed indicator of Lemma 4.1(c) is `sgn(sin p₁)` times the unsigned
mixed target used by the scalar residual of Lemma 5.4. -/
theorem signedSupportIndicator_eq_sign_mul_rawMixedTarget
    (q : Parameters) (p₁ r : ℝ) :
    signedSupportIndicator q p₁ r =
      (Real.sign (Real.sin p₁) : ℂ) * ((rawMixedTarget q |p₁| r : ℝ) : ℂ) := by
  classical
  by_cases hr : r ∈ q.supportInterval |p₁|
  · simp [signedSupportIndicator, rawMixedTarget, hr]
  · simp [signedSupportIndicator, rawMixedTarget, hr]

/-- **The mixed component of `D₁f_p`.**  The paper's `w(r,β) = i sin(r)f_p(r)`
does not depend on `β` and equals `sgn(sin p₁)1_I(r)`. -/
theorem mixedResidual_eq_sign_mul_rawMixedTarget {q : Parameters} {p₁ : ℝ}
    (hleft : 0 < q.K * q.delta |p₁|) (hright : q.r0 < Real.pi) (r : ℝ) :
    mixedResidual q p₁ r =
      (Real.sign (Real.sin p₁) : ℂ) * ((rawMixedTarget q |p₁| r : ℝ) : ℂ) := by
  rw [mixedResidual_eq_indicator hleft hright,
    signedSupportIndicator_eq_sign_mul_rawMixedTarget]

/-! ## `D̃₂*` is linear in the raw coefficient -/

/-- Scaling the raw degree-three coefficient scales its mixed `(D2b)`
component.  This is what lets the manuscript's `sgn(sin p₁)` multiplier be
carried through the lowering operator. -/
theorem rawD2StarMixed_const_mul (z : ℂ) (k : ℝ → ℝ → ℝ → ℂ) (r beta : ℝ) :
    rawD2StarMixed (fun x y b => z * k x y b) r beta =
      z * rawD2StarMixed k r beta := by
  simp only [rawD2StarMixed]
  rw [torusIntegral_const_mul]
  ring

/-! ## The competitor with the manuscript's `sgn(sin p₁)` multiplier -/

/-- **The mixed residual of the competitor of `manuscript.tex:1138-1141`.**
When the coefficient supplied by Proposition 4.2 is multiplied by
`sgn(sin p₁)` before it is called `k_p`, the mixed component of
`D₁f_p - D₂*k_p` is exactly `sgn(sin p₁)` times the scalar residual
`mixedRawResidual` of Lemma 5.4. -/
theorem mixedResidual_sub_signedCorrection {q : Parameters} {p₁ p₂ : ℝ}
    (hleft : 0 < q.K * q.delta |p₁|) (hright : q.r0 < Real.pi) (r beta : ℝ) :
    mixedResidual q p₁ r -
        rawD2StarMixed (fun x y b => (Real.sign (Real.sin p₁) : ℂ) *
          correctionCoefficient 40 q |p₁| p₂ x y b) r beta =
      (Real.sign (Real.sin p₁) : ℂ) * mixedRawResidual q |p₁| p₂ r beta := by
  rw [rawD2StarMixed_const_mul, mixedResidual_eq_sign_mul_rawMixedTarget hleft hright,
    mixedRawResidual]
  ring

/-- The `sgn(sin p₁)` multiplier is unimodular, so it moves no pointwise
norm. -/
theorem norm_mixedResidual_sub_signedCorrection {q : Parameters} {p₁ p₂ : ℝ}
    (hleft : 0 < q.K * q.delta |p₁|) (hright : q.r0 < Real.pi)
    (hsin : Real.sin p₁ ≠ 0) (r beta : ℝ) :
    ‖mixedResidual q p₁ r -
        rawD2StarMixed (fun x y b => (Real.sign (Real.sin p₁) : ℂ) *
          correctionCoefficient 40 q |p₁| p₂ x y b) r beta‖ =
      ‖mixedRawResidual q |p₁| p₂ r beta‖ := by
  rw [mixedResidual_sub_signedCorrection hleft hright, norm_mul]
  have hone : ‖((Real.sign (Real.sin p₁) : ℝ) : ℂ)‖ = 1 := by
    rcases Real.sign_apply_eq_of_ne_zero (Real.sin p₁) hsin with hs | hs <;>
      simp [hs]
  rw [hone, one_mul]

/-- **The mixed scalar energy of the signed competitor.**  With the
`sgn(sin p₁)` multiplier the mixed `H⁻¹` energy of `D₁f_p - D₂*k_p` is the
scalar quantity of Lemma 5.4. -/
theorem signedMixedResidualHMinusSq_eq {q : Parameters} {p₁ p₂ : ℝ}
    (hleft : 0 < q.K * q.delta |p₁|) (hright : q.r0 < Real.pi)
    (hsin : Real.sin p₁ ≠ 0) :
    (torusIntegral fun beta => torusIntegral fun r =>
        mixedHMinusWeight q r beta *
          ‖mixedResidual q p₁ r -
            rawD2StarMixed (fun x y b => (Real.sign (Real.sin p₁) : ℂ) *
              correctionCoefficient 40 q |p₁| p₂ x y b) r beta‖ ^ 2) =
      mixedRawResidualHMinusSq q |p₁| p₂ := by
  rw [mixedRawResidualHMinusSq]
  refine congrArg _ ?_
  funext beta
  refine congrArg _ ?_
  funext r
  rw [norm_mixedResidual_sub_signedCorrection hleft hright hsin]

/-- **Lemma 5.4 for the signed competitor.**  Proposition 4.2 bounds the mixed
scalar energy of `D₁f_p - D₂*k_p` by `C√L`.
-/
theorem signedMixedResidualHMinusSq_le_sqrtScale {q : Parameters}
    (hq : q.Admissible) {C p₁ p₂ : ℝ}
    (hleft : 0 < q.K * q.delta |p₁|) (hright : q.r0 < Real.pi)
    (hsin : Real.sin p₁ ≠ 0) (hp₂ : |p₂| ≤ |p₁|)
    (hfive : PropositionFiveTwoIntegralBound 40 C q |p₁|) :
    (torusIntegral fun beta => torusIntegral fun r =>
        mixedHMinusWeight q r beta *
          ‖mixedResidual q p₁ r -
            rawD2StarMixed (fun x y b => (Real.sign (Real.sin p₁) : ℂ) *
              correctionCoefficient 40 q |p₁| p₂ x y b) r beta‖ ^ 2) ≤
      (2 + 2 * errorKernelConstant q) * C * Real.sqrt (q.scaleLog |p₁|) := by
  rw [signedMixedResidualHMinusSq_eq hleft hright hsin]
  exact mixedRawResidualHMinusSq_le_sqrtScale hq (abs_nonneg p₁) hp₂ hfive

/-! ## Without the multiplier the two mixed components add -/

/-- **The unsigned competitor at a negative `sin p₁`.**  The mixed component of
`D₁f_p` is then `-1_I`, while `D̃₂*k̃` is a nonnegative real, so the two add
instead of cancelling. -/
theorem mixedResidual_sub_correction_of_sin_neg {q : Parameters} {p₁ p₂ : ℝ}
    (hleft : 0 < q.K * q.delta |p₁|) (hright : q.r0 < Real.pi)
    (hneg : Real.sin p₁ < 0) (r beta : ℝ) :
    mixedResidual q p₁ r -
        rawD2StarMixed (correctionCoefficient 40 q |p₁| p₂) r beta =
      -(((rawMixedTarget q |p₁| r : ℝ) : ℂ) +
        rawD2StarMixed (correctionCoefficient 40 q |p₁| p₂) r beta) := by
  rw [mixedResidual_eq_sign_mul_rawMixedTarget hleft hright, Real.sign_of_neg hneg]
  push_cast
  ring

/-- **The unsigned competitor cannot help at a negative `sin p₁`.**  The mixed
residual of `D₁f_p - D₂*k_p` is pointwise at least the uncorrected mixed
residual of Lemma 4.1(c), whose `H⁻¹` energy is of order `L`.
-/
theorem norm_mixedResidual_le_norm_sub_correction_of_sin_neg {q : Parameters}
    (hq : q.Admissible) {p₁ p₂ : ℝ} (hp₂ : |p₂| ≤ |p₁|)
    (hleft : 0 < q.K * q.delta |p₁|) (hright : q.r0 < Real.pi)
    (hneg : Real.sin p₁ < 0) (r beta : ℝ) :
    ‖mixedResidual q p₁ r‖ ≤
      ‖mixedResidual q p₁ r -
        rawD2StarMixed (correctionCoefficient 40 q |p₁| p₂) r beta‖ := by
  have hlow : (0 : ℝ) ≤ correctionSigma 40 q |p₁| r beta *
      correctionV 40 q |p₁| r beta + errorUAt q |p₁| p₂ r beta := by
    have h1 : (0 : ℝ) ≤ correctionSigma 40 q |p₁| r beta :=
      correctionSigma_nonneg (q := q) (kappa := 40) (by norm_num) hq.1 |p₁| r beta
    have h2 : (0 : ℝ) ≤ correctionV 40 q |p₁| r beta :=
      correctionV_nonneg hq |p₁| r beta
    have h3 : (0 : ℝ) ≤ errorUAt q |p₁| p₂ r beta := errorUAt_nonneg hq |p₁| p₂ r beta
    positivity
  have htarget : (0 : ℝ) ≤ rawMixedTarget q |p₁| r := by
    rw [rawMixedTarget]
    split_ifs with h
    · exact zero_le_one
    · exact le_rfl
  have hD : rawD2StarMixed (correctionCoefficient 40 q |p₁| p₂) r beta =
      ((correctionSigma 40 q |p₁| r beta * correctionV 40 q |p₁| r beta +
        errorUAt q |p₁| p₂ r beta : ℝ) : ℂ) :=
    rawD2StarMixed_correction_eq hq (abs_nonneg p₁) hp₂ r beta
  rw [mixedResidual_sub_correction_of_sin_neg hleft hright hneg,
    mixedResidual_eq_sign_mul_rawMixedTarget hleft hright, Real.sign_of_neg hneg, hD]
  rw [show (-((((rawMixedTarget q |p₁| r : ℝ)) : ℂ) +
      ((correctionSigma 40 q |p₁| r beta * correctionV 40 q |p₁| r beta +
        errorUAt q |p₁| p₂ r beta : ℝ) : ℂ))) =
      (((-(rawMixedTarget q |p₁| r +
        (correctionSigma 40 q |p₁| r beta * correctionV 40 q |p₁| r beta +
          errorUAt q |p₁| p₂ r beta)) : ℝ)) : ℂ) by push_cast; ring]
  rw [show ((((-1 : ℝ)) : ℂ) * ((rawMixedTarget q |p₁| r : ℝ) : ℂ)) =
      (((-(rawMixedTarget q |p₁| r) : ℝ)) : ℂ) by push_cast; ring]
  rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_neg, abs_neg, abs_of_nonneg htarget,
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ rawMixedTarget q |p₁| r +
      (correctionSigma 40 q |p₁| r beta * correctionV 40 q |p₁| r beta +
        errorUAt q |p₁| p₂ r beta))]
  linarith

end

end Manhattan.Glue
