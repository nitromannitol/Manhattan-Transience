import Manhattan.Estimates.TargetStatements

/-!
# Final integration step in Proposition 4.2

This module proves that the beta-integral estimate (34) implies the final
`r`-integral bound in Proposition 4.2, with the same constant.  It isolates
the logarithmic change of variables at `manuscript.tex:1121-1125` from the
still-open pointwise denominator and beta-splitting estimates.
-/

open MeasureTheory Set

namespace Manhattan.Estimates

noncomputable section

/-- Classical decidability, local to this file: the statements here are analytic, not computational. -/
local instance propositionFiveTwoPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

private theorem normalizedFactor_pos : 0 < (2 * Real.pi)⁻¹ := by positivity

/-- Equation (34) integrates in `r` to the last analytic bound of Proposition
4.2. -/
theorem propositionFiveTwoIntegralBound_of_betaIntegralBound
    {q : Parameters} {C a : ℝ} (hq : q.Admissible) (hC : 0 ≤ C) (ha : 0 ≤ a)
    (hsupport : q.K * q.delta a < q.r0) (hbeta : BetaIntegralBound 40 C q a) :
    PropositionFiveTwoIntegralBound 40 C q a := by
  let left : ℝ := q.K * q.delta a
  let base : ℝ → ℝ := fun r => C / (r * Real.sqrt (1 + Real.log (q.r0 / r)))
  let inner : ℝ → ℝ := fun r => torusIntegral (fun beta : ℝ =>
    (correctionB q r beta + correctionSigma 40 q a r beta)⁻¹)
  let g : ℝ → ℝ := fun r => if r ∈ q.supportInterval a then inner r else 0
  let majorant : ℝ → ℝ := fun r => if r ∈ q.supportInterval a then base r else 0
  have hleftPos : 0 < left := by
    apply mul_pos (by linarith [hq.2.2.1])
    exact add_pos_of_pos_of_nonneg (Real.sqrt_pos.2 hq.1) ha
  have hr0Pos : 0 < q.r0 := by
    dsimp [Parameters.r0]
    exact div_pos hq.2.2.2.1 (mul_pos (by norm_num) (by linarith [hq.2.2.1]))
  have hleftLe : left ≤ q.r0 := hsupport.le
  have hr0Pi : q.r0 < Real.pi := by
    dsimp [Parameters.r0]
    have hKPos : 0 < q.K := by linarith [hq.2.2.1]
    have hden : 0 < 100 * q.K := by positivity
    have hquotient : q.rho / (100 * q.K) ≤ (Real.pi / 20) / (100 * q.K) := by
      exact div_le_div_of_nonneg_right hq.2.2.2.2 hden.le
    have hsmall : (Real.pi / 20) / (100 * q.K) < Real.pi := by
      rw [div_lt_iff₀ hden]
      apply mul_lt_mul_of_pos_left _ Real.pi_pos
      nlinarith [hq.2.2.1]
    exact hquotient.trans_lt hsmall
  have hintervalSubset : q.supportInterval a ⊆ torus := by
    intro r hr
    exact ⟨(neg_lt_zero.mpr Real.pi_pos).trans (hleftPos.trans_le hr.1),
      hr.2.trans_lt hr0Pi |>.le⟩
  have hbaseCont : ContinuousOn base (q.supportInterval a) := by
    intro r hr
    have hrPos : 0 < r := hleftPos.trans_le hr.1
    have hratioPos : 0 < q.r0 / r := div_pos hr0Pos hrPos
    have hlogNonneg : 0 ≤ Real.log (q.r0 / r) := by
      apply Real.log_nonneg
      exact (le_div_iff₀ hrPos).2 (by simpa using hr.2)
    have hsqrtPos : 0 < Real.sqrt (1 + Real.log (q.r0 / r)) :=
      Real.sqrt_pos.2 (by linarith)
    apply ContinuousAt.continuousWithinAt
    dsimp [base]
    apply ContinuousAt.div continuousAt_const
    · have hdivCont : ContinuousAt (fun x : ℝ => q.r0 / x) r :=
        continuousAt_const.div continuousAt_id hrPos.ne'
      have hlogCont : ContinuousAt (fun x : ℝ => Real.log (q.r0 / x)) r :=
        hdivCont.log hratioPos.ne'
      exact continuousAt_id.mul (continuousAt_const.add hlogCont).sqrt
    · exact mul_ne_zero hrPos.ne' hsqrtPos.ne'
  have hmajorantIntVolume : Integrable majorant volume := by
    have hbaseInt : IntegrableOn base (q.supportInterval a) := by
      simpa only [Parameters.supportInterval] using hbaseCont.integrableOn_Icc
    have hint := hbaseInt.integrable_indicator measurableSet_Icc
    simpa only [majorant, Set.indicator_apply] using hint
  have hmajorantInt : Integrable majorant (volume.restrict torus) :=
    hmajorantIntVolume.mono_measure Measure.restrict_le_self
  have hpoint : ∀ r : ℝ, g r ≤ majorant r := by
    intro r
    by_cases hr : r ∈ q.supportInterval a
    · simpa only [g, majorant, if_pos hr, inner, base] using hbeta r hr
    · simp [g, majorant, hr]
  have hjointMeasurable : Measurable (fun z : ℝ × ℝ =>
      (correctionB q z.1 z.2 + correctionSigma 40 q a z.1 z.2)⁻¹) := by
    have hB : Measurable (fun z : ℝ × ℝ => correctionB q z.1 z.2) := by
      unfold correctionB dispersion
      fun_prop
    exact (hB.add (correctionSigma_measurable 40 q a)).inv
  have hinnerMeasurable : Measurable inner := by
    dsimp [inner, torusIntegral]
    exact (hjointMeasurable.stronglyMeasurable.integral_prod_right.measurable.const_mul
      (2 * Real.pi)⁻¹)
  have hgMeasurable : Measurable g := by
    dsimp [g]
    exact Measurable.ite measurableSet_Icc hinnerMeasurable measurable_const
  have hinnerNonneg : ∀ r : ℝ, 0 ≤ inner r := by
    intro r
    dsimp [inner, torusIntegral]
    apply mul_nonneg normalizedFactor_pos.le
    apply integral_nonneg
    intro beta
    exact (inv_pos.mpr (correctionDenominator_pos (by norm_num) hq.1 a r beta)).le
  have hgNonneg : ∀ r : ℝ, 0 ≤ g r := by
    intro r
    dsimp [g]
    split_ifs
    · exact hinnerNonneg r
    · exact le_rfl
  have hg : Integrable g (volume.restrict torus) := by
    apply Integrable.mono' hmajorantInt hgMeasurable.aestronglyMeasurable
    filter_upwards with r
    rw [Real.norm_eq_abs, abs_of_nonneg (hgNonneg r)]
    exact hpoint r
  have htorusMajorize : torusIntegral g ≤ torusIntegral majorant := by
    rw [torusIntegral, torusIntegral]
    simp only [smul_eq_mul]
    apply mul_le_mul_of_nonneg_left _ normalizedFactor_pos.le
    exact integral_mono hg hmajorantInt hpoint
  apply htorusMajorize.trans
  have hmajorantIntegral : torusIntegral majorant =
      (2 * Real.pi)⁻¹ * C *
        (∫ r in left..q.r0, (r * Real.sqrt (1 + Real.log (q.r0 / r)))⁻¹) := by
    rw [torusIntegral]
    simp only [smul_eq_mul]
    change (2 * Real.pi)⁻¹ * (∫ r,
      (q.supportInterval a).indicator base r ∂volume.restrict torus) = _
    have hsupportMeas : MeasurableSet (q.supportInterval a) := measurableSet_Icc
    rw [integral_indicator hsupportMeas]
    rw [Measure.restrict_restrict hsupportMeas]
    rw [inter_eq_left.mpr hintervalSubset]
    simp only [Parameters.supportInterval]
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hleftLe]
    simp only [base, div_eq_mul_inv]
    rw [intervalIntegral.integral_const_mul]
    ring
  rw [hmajorantIntegral]
  have hlogLe : 1 + Real.log (q.r0 / left) ≤ q.scaleLog a := by
    have hdeltaPos : 0 < q.delta a :=
      add_pos_of_pos_of_nonneg (Real.sqrt_pos.2 hq.1) ha
    have hKOne : 1 ≤ q.K := by linarith [hq.2.2.1]
    have hdeltaLe : q.delta a ≤ left := by
      dsimp [left]
      nlinarith
    have hdivLe : q.r0 / left ≤ q.r0 / q.delta a := by
      exact div_le_div_of_nonneg_left hr0Pos.le hdeltaPos hdeltaLe
    have hlogRatioLe : Real.log (q.r0 / left) ≤ Real.log (q.r0 / q.delta a) :=
      Real.log_le_log (div_pos hr0Pos hleftPos) hdivLe
    dsimp [Parameters.scaleLog]
    simpa only [logPos, add_comm] using
      add_le_add_left (hlogRatioLe.trans (le_max_right _ _)) 1
  have hsqrtLe : Real.sqrt (1 + Real.log (q.r0 / left)) ≤
      Real.sqrt (q.scaleLog a) := Real.sqrt_le_sqrt hlogLe
  have hlogIntegral := logScaleIntegral_le hleftPos hleftLe
  have hcoeff : (2 * Real.pi)⁻¹ * 2 ≤ 1 := by
    have hpiOne : 1 ≤ Real.pi := by linarith [Real.two_le_pi]
    calc
      (2 * Real.pi)⁻¹ * 2 = Real.pi⁻¹ := by field_simp [Real.pi_ne_zero]
      _ ≤ 1 := (inv_le_one₀ Real.pi_pos).2 hpiOne
  calc
    (2 * Real.pi)⁻¹ * C *
        (∫ r in left..q.r0, (r * Real.sqrt (1 + Real.log (q.r0 / r)))⁻¹) ≤
        (2 * Real.pi)⁻¹ * C *
          (2 * Real.sqrt (1 + Real.log (q.r0 / left))) := by gcongr
    _ ≤ (2 * Real.pi)⁻¹ * C * (2 * Real.sqrt (q.scaleLog a)) := by gcongr
    _ ≤ C * Real.sqrt (q.scaleLog a) := by
      calc
        _ = ((2 * Real.pi)⁻¹ * 2) * (C * Real.sqrt (q.scaleLog a)) := by ring
        _ ≤ 1 * (C * Real.sqrt (q.scaleLog a)) := by gcongr
        _ = _ := one_mul _

/-- Once the pointwise denominator estimate (33) and the beta-integral
estimate (34) are available with uniform constants, the preceding theorem
supplies the final conjunct of `PropositionFiveTwoClaim`.  This records the
exact remaining interface: no further two-dimensional integration estimate
is needed. -/
-- INTERFACE: supply equations (33) and (34), uniformly in `lambda` and `a`.
theorem propositionFiveTwoClaim_of_denominator_and_beta_bounds
    (K rho c C : ℝ) (hc : 0 < c) (hC : 0 < C)
    (hbounds : ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 →
      ∀ (a : ℝ), 0 ≤ a →
        let q : Parameters := ⟨lambda, K, rho⟩
        K * q.delta a < q.r0 →
          DenominatorBound 40 c q a ∧ BetaIntegralBound 40 C q a) :
    PropositionFiveTwoClaim K rho := by
  intro hK hrhoPos hrho
  refine ⟨c, C, hc, hC, ?_⟩
  intro lambda hlambda hlambdaOne a ha
  dsimp only
  let q : Parameters := ⟨lambda, K, rho⟩
  intro hsupport
  have hq : q.Admissible :=
    ⟨hlambda, hlambdaOne, hK, hrhoPos, hrho⟩
  obtain ⟨hdenominator, hbeta⟩ :=
    hbounds lambda hlambda hlambdaOne a ha hsupport
  exact ⟨hdenominator, hbeta,
    propositionFiveTwoIntegralBound_of_betaIntegralBound
      hq hC.le ha hsupport hbeta⟩

end

end Manhattan.Estimates
