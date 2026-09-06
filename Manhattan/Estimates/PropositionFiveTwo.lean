import Manhattan.Estimates.PropositionFiveTwoSupport
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Completion of Proposition 4.2

This module proves the denominator estimate (33), the beta integral estimate
(34), and packages them as the provider for the frozen Proposition 4.2
anchor.  Constants are deliberately explicit and uniform in `lambda` and the
frequency scale `a`.

Paper: `manuscript.tex:1068-1127`.
-/

open MeasureTheory Set

namespace Manhattan.Estimates

noncomputable section

/-- Classical decidability, local to this file: the statements here are analytic, not computational. -/
local instance propositionFiveTwoCompletionPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

private theorem normalizedFactor_le_one : (2 * Real.pi)⁻¹ ≤ 1 := by
  exact (inv_le_one₀ (by positivity)).2 (by linarith [Real.two_le_pi])

private theorem r0_pos_of_admissible {q : Parameters} (hq : q.Admissible) :
    0 < q.r0 := by
  rw [Parameters.r0]
  exact div_pos hq.2.2.2.1 (mul_pos (by norm_num) (by linarith [hq.2.2.1]))

private theorem r0_lt_pi_of_admissible {q : Parameters} (hq : q.Admissible) :
    q.r0 < Real.pi := by
  rw [Parameters.r0]
  have hKPos : 0 < q.K := by linarith [hq.2.2.1]
  have hden : 0 < 100 * q.K := mul_pos (by norm_num) hKPos
  have hquotient : q.rho / (100 * q.K) ≤ (Real.pi / 20) / (100 * q.K) :=
    div_le_div_of_nonneg_right hq.2.2.2.2 hden.le
  have hsmall : (Real.pi / 20) / (100 * q.K) < Real.pi := by
    rw [div_lt_iff₀ hden]
    apply mul_lt_mul_of_pos_left _ Real.pi_pos
    nlinarith [hq.2.2.1]
  exact hquotient.trans_lt hsmall

private theorem delta_pos_of_admissible {q : Parameters} (hq : q.Admissible)
    {a : ℝ} (ha : 0 ≤ a) : 0 < q.delta a := by
  rw [Parameters.delta]
  exact add_pos_of_pos_of_nonneg (Real.sqrt_pos.2 hq.1) ha

private theorem support_subset_torus {q : Parameters} (hq : q.Admissible)
    {a : ℝ} (ha : 0 ≤ a) : q.supportInterval a ⊆ torus := by
  intro r hr
  have hleft : 0 < q.K * q.delta a :=
    mul_pos (by linarith [hq.2.2.1]) (delta_pos_of_admissible hq ha)
  exact ⟨(neg_lt_zero.mpr Real.pi_pos).trans (hleft.trans_le hr.1),
    (hr.2.trans_lt (r0_lt_pi_of_admissible hq)).le⟩

private theorem torusIntegral_indicator_eq_setIntegral
    (f : ℝ → ℝ) {s : Set ℝ} (hs : MeasurableSet s) (hst : s ⊆ torus) :
    torusIntegral (fun x : ℝ => if x ∈ s then f x else 0) =
      (2 * Real.pi)⁻¹ * ∫ x in s, f x := by
  rw [torusIntegral]
  simp only [smul_eq_mul]
  change (2 * Real.pi)⁻¹ * (∫ x in torus, s.indicator f x) = _
  rw [integral_indicator hs, Measure.restrict_restrict hs,
    inter_eq_left.mpr hst]

theorem torusIntegral_cauchy_le {A D : ℝ} (hA : 0 < A) (hD : 0 < D) :
    torusIntegral (fun x : ℝ => (A ^ 2 + D ^ 2 * x ^ 2)⁻¹) ≤
      1 / (A * D) := by
  let c : ℝ := D / A
  have hc : 0 < c := div_pos hD hA
  have hcNe : c ≠ 0 := hc.ne'
  have hpoint : ∀ x : ℝ,
      (A ^ 2 + D ^ 2 * x ^ 2)⁻¹ =
        (A ^ 2)⁻¹ * (1 + (c * x) ^ 2)⁻¹ := by
    intro x
    dsimp [c]
    field_simp [hA.ne', hD.ne']
  have harctan : Real.arctan (c * Real.pi) - Real.arctan (c * (-Real.pi)) ≤
      Real.pi := by
    linarith [Real.arctan_lt_pi_div_two (c * Real.pi),
      Real.neg_pi_div_two_lt_arctan (c * (-Real.pi))]
  rw [torusIntegral, torus,
    ← intervalIntegral.integral_of_le (le_of_lt (neg_lt_self Real.pi_pos))]
  simp only [smul_eq_mul]
  calc
    (2 * Real.pi)⁻¹ *
        (∫ x in -Real.pi..Real.pi, (A ^ 2 + D ^ 2 * x ^ 2)⁻¹) =
        (2 * Real.pi)⁻¹ * (A ^ 2)⁻¹ *
          (c⁻¹ * (Real.arctan (c * Real.pi) -
            Real.arctan (c * (-Real.pi)))) := by
              rw [intervalIntegral.integral_congr (fun x _ => hpoint x),
                intervalIntegral.integral_const_mul,
                intervalIntegral.integral_comp_mul_left
                  (f := fun y : ℝ => (1 + y ^ 2)⁻¹) hcNe,
                integral_inv_one_add_sq]
              simp only [smul_eq_mul]
              ring
    _ ≤ (2 * Real.pi)⁻¹ * (A ^ 2)⁻¹ * (c⁻¹ * Real.pi) := by gcongr
    _ ≤ 1 / (A * D) := by
      dsimp [c]
      field_simp [hA.ne', hD.ne', Real.pi_ne_zero]
      nlinarith [Real.pi_pos]

private theorem torusIntegral_const_mul (c : ℝ) (f : ℝ → ℝ) :
    torusIntegral (fun x => c * f x) = c * torusIntegral f := by
  simp only [torusIntegral, integral_const_mul, smul_eq_mul]
  ring

private theorem torusIntegral_add_of_integrable {f g : ℝ → ℝ}
    (hf : Integrable f (volume.restrict torus))
    (hg : Integrable g (volume.restrict torus)) :
    torusIntegral (fun x => f x + g x) = torusIntegral f + torusIntegral g := by
  simp only [torusIntegral, integral_add hf hg, smul_eq_mul]
  ring

private theorem correctionB_quadratic_lower {q : Parameters} (hq : q.Admissible)
    {a r beta : ℝ} (ha : 0 ≤ a) (hr : r ∈ q.supportInterval a)
    (hbeta : beta ∈ torus) :
    (1 / 8 : ℝ) * (q.lambda + r ^ 2 + beta ^ 2) ≤ correctionB q r beta := by
  have hrTorus := support_subset_torus hq ha hr
  have hrAbs : |r| ≤ Real.pi := (abs_le).2 ⟨hrTorus.1.le, hrTorus.2⟩
  have hbetaAbs : |beta| ≤ Real.pi := (abs_le).2 ⟨hbeta.1.le, hbeta.2⟩
  have hdr := (dispersion_quadratic_bounds hrAbs).1
  have hdbeta := (dispersion_quadratic_bounds hbetaAbs).1
  have hcpi : (1 / 8 : ℝ) ≤ 2 / Real.pi ^ 2 := by
    rw [le_div_iff₀ (sq_pos_of_pos Real.pi_pos)]
    nlinarith [Real.pi_le_four, Real.pi_pos]
  have hlambda : (1 / 8 : ℝ) * q.lambda ≤ q.lambda := by
    nlinarith [hq.1]
  have hdr' : (1 / 8 : ℝ) * r ^ 2 ≤ dispersion r := by
    calc
      (1 / 8 : ℝ) * r ^ 2 ≤ (2 / Real.pi ^ 2) * r ^ 2 := by gcongr
      _ = 2 * r ^ 2 / Real.pi ^ 2 := by ring
      _ ≤ dispersion r := hdr
  have hdbeta' : (1 / 8 : ℝ) * beta ^ 2 ≤ dispersion beta := by
    calc
      (1 / 8 : ℝ) * beta ^ 2 ≤ (2 / Real.pi ^ 2) * beta ^ 2 := by gcongr
      _ = 2 * beta ^ 2 / Real.pi ^ 2 := by ring
      _ ≤ dispersion beta := hdbeta
  rw [correctionB]
  linarith

private theorem correctionSigma_log_lower {q : Parameters} (hq : q.Admissible)
    {a r beta : ℝ} (ha : 0 ≤ a) (hr : r ∈ q.supportInterval a)
    (_hbeta : beta ∈ torus) :
    (1 / (1600 * Real.pi)) * beta ^ 2 *
        logPos (q.r0 / (r + |beta|)) ≤ correctionSigma 40 q a r beta := by
  have hsigmaNonneg := correctionSigma_nonneg (q := q) (kappa := 40)
    (by norm_num) hq.1 a r beta
  by_cases hactive : r + |beta| < q.r0
  · have hKPos : 0 < q.K := by linarith [hq.2.2.1]
    have hdeltaPos : 0 < q.delta a := delta_pos_of_admissible hq ha
    have hrPos : 0 < r :=
      (mul_pos hKPos hdeltaPos).trans_le hr.1
    have htPos : 0 < r + |beta| := add_pos_of_pos_of_nonneg hrPos (abs_nonneg _)
    have hdeltaLe : q.delta a ≤ r / q.K := by
      rw [le_div_iff₀ hKPos]
      simpa only [mul_comm] using hr.1
    have hdeltaLeR : q.delta a ≤ r := by
      have hKOne : 1 ≤ q.K := by linarith [hq.2.2.1]
      exact hdeltaLe.trans (div_le_self hrPos.le hKOne)
    let u : ℝ := 4 * q.K * (r + q.delta a + |beta|)
    have huPos : 0 < u := by
      dsimp [u]
      positivity
    have hsumLe : r + q.delta a + |beta| ≤ 2 * (r + |beta|) := by
      linarith [abs_nonneg beta]
    have hcondition : r + q.delta a + |beta| ≤ q.rho / (8 * q.K) := by
      have hr0Eq : q.rho = 100 * q.K * q.r0 := by
        rw [Parameters.r0]
        field_simp [hKPos.ne']
      apply (le_div_iff₀ (mul_pos (by norm_num) hKPos)).2
      rw [hr0Eq]
      nlinarith [hactive]
    have hinter : correctionInterval q a r beta = Set.Icc (-q.rho) (-u) := by
      simp [correctionInterval, hr, hcondition, u]
    have huRho : u < q.rho := by
      have hr0Eq : q.rho = 100 * q.K * q.r0 := by
        rw [Parameters.r0]
        field_simp [hKPos.ne']
      dsimp [u]
      rw [hr0Eq]
      nlinarith [hactive, hsumLe]
    have hJSubset : Set.Icc (-q.rho) (-u) ⊆ torus := by
      intro alpha halpha
      have hrhoPi : q.rho < Real.pi :=
        hq.2.2.2.2.trans_lt (by nlinarith [Real.pi_pos])
      exact ⟨(neg_lt_neg hrhoPi).trans_le halpha.1,
        (halpha.2.trans (neg_nonpos.mpr huPos.le)).trans Real.pi_pos.le⟩
    have hMPos : ∀ alpha ∈ Set.Icc (-q.rho) (-u),
        0 < multiplier 40 q (mixedTotalFrequency beta alpha) := by
      intro alpha _
      exact multiplier_pos (by norm_num) hq.1 _
    have hpoint : ∀ alpha ∈ Set.Icc (-q.rho) (-u),
        (200 * |alpha|)⁻¹ ≤
          (multiplier 40 q (mixedTotalFrequency beta alpha))⁻¹ := by
      intro alpha halpha
      have halphaNonpos : alpha < 0 := halpha.2.trans_lt (neg_lt_zero.mpr huPos)
      have habs : |alpha| = -alpha := abs_of_neg halphaNonpos
      have halphaRho : |alpha| ≤ q.rho := by
        rw [habs]
        linarith [halpha.1]
      have hseparation : 4 * q.K * (Real.sqrt q.lambda + |beta|) ≤ |alpha| := by
        rw [habs]
        dsimp [u] at halpha
        rw [Parameters.delta] at halpha
        nlinarith [halpha.2, hrPos, hKPos]
      have hupper := (multiplier_comparison_explicit hq.2.2.1 hq.2.2.2.2 hq.1
        hq.2.1 halphaRho hseparation).2
      exact (inv_le_inv₀ (mul_pos (by norm_num) (abs_pos.mpr halphaNonpos.ne))
        (hMPos alpha halpha)).2 hupper
    have hlowerCont : ContinuousOn (fun alpha : ℝ => (200 * |alpha|)⁻¹)
        (Set.Icc (-q.rho) (-u)) := by
      apply ContinuousOn.inv₀
      · fun_prop
      · intro alpha halpha
        have halphaNeg : alpha < 0 := halpha.2.trans_lt (neg_lt_zero.mpr huPos)
        exact mul_ne_zero (by norm_num) (abs_ne_zero.mpr halphaNeg.ne)
    have hMCont : Continuous (fun alpha : ℝ =>
        multiplier 40 q (mixedTotalFrequency beta alpha)) := by
      simp only [multiplier, mixedTotalFrequency, theta, Matrix.cons_val_zero,
        Matrix.cons_val_one, dispersion]
      fun_prop
    have hinvMCont : Continuous (fun alpha : ℝ =>
        (multiplier 40 q (mixedTotalFrequency beta alpha))⁻¹) := by
      apply Continuous.inv₀ hMCont
      intro alpha
      exact (multiplier_pos (by norm_num) hq.1 _).ne'
    have hintegralLower :
        (∫ alpha in Set.Icc (-q.rho) (-u), (200 * |alpha|)⁻¹) ≤
          ∫ alpha in Set.Icc (-q.rho) (-u),
            (multiplier 40 q (mixedTotalFrequency beta alpha))⁻¹ := by
      exact setIntegral_mono_on hlowerCont.integrableOn_Icc
        hinvMCont.continuousOn.integrableOn_Icc measurableSet_Icc hpoint
    have htorusLower :
        (2 * Real.pi)⁻¹ *
            (∫ alpha in Set.Icc (-q.rho) (-u), (200 * |alpha|)⁻¹) ≤
          torusIntegral (fun alpha : ℝ =>
            if alpha ∈ correctionInterval q a r beta then
              (multiplier 40 q (mixedTotalFrequency beta alpha))⁻¹ else 0) := by
      rw [hinter, torusIntegral_indicator_eq_setIntegral _ measurableSet_Icc hJSubset]
      exact mul_le_mul_of_nonneg_left hintegralLower (by positivity)
    have hlowerIntegral :
        (∫ alpha in Set.Icc (-q.rho) (-u), (200 * |alpha|)⁻¹) =
          (1 / 200) * Real.log (q.rho / u) := by
      rw [integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by linarith [huRho])]
      have hrhoPos := hq.2.2.2.1
      calc
        (∫ alpha in -q.rho..-u, (200 * |alpha|)⁻¹) =
            (1 / 200) * ∫ alpha in -q.rho..-u, (-alpha)⁻¹ := by
              rw [← intervalIntegral.integral_const_mul]
              apply intervalIntegral.integral_congr
              intro alpha halpha
              have halphaNeg : alpha < 0 := by
                rw [Set.uIcc_of_le (by linarith [huRho])] at halpha
                exact halpha.2.trans_lt (neg_lt_zero.mpr huPos)
              change (200 * |alpha|)⁻¹ = 1 / 200 * (-alpha)⁻¹
              rw [abs_of_neg halphaNeg]
              field_simp
        _ = (1 / 200) * ∫ x in u..q.rho, x⁻¹ := by
              rw [intervalIntegral.integral_comp_neg]
              simp only [neg_neg]
        _ = (1 / 200) * Real.log (q.rho / u) := by
              rw [integral_inv_of_pos huPos hrhoPos]
    have hratio : q.r0 / (r + |beta|) ≤ q.rho / u := by
      have huLe : u ≤ 8 * q.K * (r + |beta|) := by
        dsimp [u]
        nlinarith [hKPos, hsumLe]
      have hr0Eq : q.rho = 100 * q.K * q.r0 := by
        rw [Parameters.r0]
        field_simp [hKPos.ne']
      rw [div_le_div_iff₀ htPos huPos]
      rw [hr0Eq]
      nlinarith [r0_pos_of_admissible hq, hKPos, htPos, huLe]
    have hlogLe : logPos (q.r0 / (r + |beta|)) ≤ Real.log (q.rho / u) := by
      have hxOne : 1 < q.r0 / (r + |beta|) :=
        (one_lt_div htPos).2 hactive
      rw [logPos, max_eq_right (Real.log_pos hxOne).le]
      exact Real.log_le_log (div_pos (r0_pos_of_admissible hq) htPos) hratio
    have hsinLower : beta ^ 2 / 4 ≤ Real.sin beta ^ 2 := by
      have hbetaAbs : |beta| ≤ Real.pi / 2 := by
        have hr0Rho : q.r0 ≤ q.rho := by
          rw [Parameters.r0]
          exact div_le_self hq.2.2.2.1.le (by nlinarith [hq.2.2.1])
        have hr0Small : q.r0 ≤ Real.pi / 2 :=
          hr0Rho.trans (hq.2.2.2.2.trans (by nlinarith [Real.pi_pos]))
        linarith [hactive, hrPos]
      have hjordan := Real.mul_abs_le_abs_sin hbetaAbs
      have hhalf : |beta| / 2 ≤ |Real.sin beta| := by
        calc
          |beta| / 2 ≤ (2 / Real.pi) * |beta| := by
            have : (1 / 2 : ℝ) ≤ 2 / Real.pi := by
              rw [le_div_iff₀ Real.pi_pos]
              nlinarith [Real.pi_le_four]
            simpa only [div_eq_mul_inv, one_mul, mul_comm] using
              mul_le_mul_of_nonneg_right this (abs_nonneg beta)
          _ ≤ |Real.sin beta| := hjordan
      have hsquare := mul_self_le_mul_self (by positivity : 0 ≤ |beta| / 2) hhalf
      calc
        beta ^ 2 / 4 = (|beta| / 2) * (|beta| / 2) := by
          rw [← sq_abs beta]
          ring
        _ ≤ |Real.sin beta| * |Real.sin beta| := hsquare
        _ = Real.sin beta ^ 2 := by rw [← sq_abs (Real.sin beta)]; ring
    rw [correctionSigma]
    calc
      (1 / (1600 * Real.pi)) * beta ^ 2 *
          logPos (q.r0 / (r + |beta|)) ≤
          Real.sin beta ^ 2 * ((2 * Real.pi)⁻¹ *
            ((1 / 200) * Real.log (q.rho / u))) := by
              have hlogNonneg : 0 ≤ logPos (q.r0 / (r + |beta|)) :=
                le_max_left _ _
              have hlogRhoNonneg : 0 ≤ Real.log (q.rho / u) := hlogLe.trans' hlogNonneg
              calc
                (1 / (1600 * Real.pi)) * beta ^ 2 *
                    logPos (q.r0 / (r + |beta|)) =
                    (beta ^ 2 / 4) * ((2 * Real.pi)⁻¹ *
                      ((1 / 200) * logPos (q.r0 / (r + |beta|)))) := by
                        field_simp [Real.pi_ne_zero]
                        ring
                _ ≤ Real.sin beta ^ 2 * ((2 * Real.pi)⁻¹ *
                      ((1 / 200) * logPos (q.r0 / (r + |beta|)))) := by gcongr
                _ ≤ Real.sin beta ^ 2 * ((2 * Real.pi)⁻¹ *
                      ((1 / 200) * Real.log (q.rho / u))) := by gcongr
      _ = Real.sin beta ^ 2 * ((2 * Real.pi)⁻¹ *
            (∫ alpha in Set.Icc (-q.rho) (-u), (200 * |alpha|)⁻¹)) := by
              rw [hlowerIntegral]
      _ ≤ Real.sin beta ^ 2 * torusIntegral (fun alpha : ℝ =>
            if alpha ∈ correctionInterval q a r beta then
              (multiplier 40 q (mixedTotalFrequency beta alpha))⁻¹ else 0) := by
              exact mul_le_mul_of_nonneg_left htorusLower (sq_nonneg _)
  · have htPos : 0 < r + |beta| := by
      have hrPos : 0 < r :=
        (mul_pos (by linarith [hq.2.2.1]) (delta_pos_of_admissible hq ha)).trans_le hr.1
      positivity
    have hratioLe : q.r0 / (r + |beta|) ≤ 1 := by
      exact (div_le_one htPos).2 (le_of_not_gt hactive)
    have hlogNonpos : Real.log (q.r0 / (r + |beta|)) ≤ 0 :=
      Real.log_nonpos (div_nonneg (r0_pos_of_admissible hq).le htPos.le) hratioLe
    simpa [logPos, max_eq_left hlogNonpos] using hsigmaNonneg

/-- Equation (33), with the explicit uniform constant `1 / (4000π)`. -/
theorem denominatorBound_proved {q : Parameters} (hq : q.Admissible)
    {a : ℝ} (ha : 0 ≤ a) : DenominatorBound 40 (1 / (4000 * Real.pi)) q a := by
  intro r hr beta hbeta
  have hbase := correctionB_quadratic_lower hq ha hr hbeta
  have hlog := correctionSigma_log_lower hq ha hr hbeta
  have hcBase : 1 / (4000 * Real.pi) ≤ (1 / 8 : ℝ) := by
    rw [div_le_iff₀ (mul_pos (by norm_num) Real.pi_pos)]
    nlinarith [Real.two_le_pi]
  have hcLog : 1 / (4000 * Real.pi) ≤ 1 / (1600 * Real.pi) := by
    rw [div_le_div_iff₀ (show 0 < 4000 * Real.pi by positivity)
      (show 0 < 1600 * Real.pi by positivity)]
    nlinarith [Real.pi_pos]
  have hbaseNonneg : 0 ≤ q.lambda + r ^ 2 + beta ^ 2 :=
    add_nonneg (add_nonneg hq.1.le (sq_nonneg _)) (sq_nonneg _)
  have hlogNonneg : 0 ≤ beta ^ 2 * logPos (q.r0 / (r + |beta|)) :=
    mul_nonneg (sq_nonneg _) (le_max_left _ _)
  nlinarith

set_option maxHeartbeats 1600000
/-- Equation (34), with a deliberately round uniform constant. -/
theorem betaIntegralBound_proved {q : Parameters} (hq : q.Admissible)
    {a : ℝ} (ha : 0 ≤ a) : BetaIntegralBound 40 200000 q a := by
  intro r hr
  let L : ℝ := 1 + Real.log (q.r0 / r)
  let g : ℝ → ℝ := fun beta =>
    (correctionB q r beta + correctionSigma 40 q a r beta)⁻¹
  have hrPos : 0 < r := by
    exact (mul_pos (by linarith [hq.2.2.1]) (delta_pos_of_admissible hq ha)).trans_le hr.1
  have hr0Pos : 0 < q.r0 := r0_pos_of_admissible hq
  have hratioOne : 1 ≤ q.r0 / r := (le_div_iff₀ hrPos).2 (by simpa using hr.2)
  have hlogNonneg : 0 ≤ Real.log (q.r0 / r) := Real.log_nonneg hratioOne
  have hLPos : 0 < L := by dsimp [L]; linarith
  have hsqrtLPos : 0 < Real.sqrt L := Real.sqrt_pos.2 hLPos
  have hrightPos : 0 < r * Real.sqrt L := mul_pos hrPos hsqrtLPos
  have hgNonneg : ∀ beta : ℝ, 0 ≤ g beta := by
    intro beta
    dsimp [g]
    exact (inv_pos.2 (correctionDenominator_pos (by norm_num) hq.1 a r beta)).le
  have hgMeasurable : Measurable g := by
    have hB : Measurable (fun beta : ℝ => correctionB q r beta) := by
      unfold correctionB dispersion
      fun_prop
    have hsigma : Measurable (fun beta : ℝ => correctionSigma 40 q a r beta) :=
      correctionSigma_measurable_right 40 q a r
    dsimp [g]
    exact (hB.add hsigma).inv
  letI : IsFiniteMeasure (volume.restrict torus) := ⟨by
    rw [Measure.restrict_apply_univ, torus]
    exact measure_Ioc_lt_top⟩
  have hgProved : Integrable g (volume.restrict torus) := by
    apply Integrable.of_bound hgMeasurable.aestronglyMeasurable q.lambda⁻¹
    filter_upwards with beta
    have hdenPos := correctionDenominator_pos (q := q) (kappa := 40)
      (by norm_num) hq.1 a r beta
    have hdenLower : q.lambda ≤
        correctionB q r beta + correctionSigma 40 q a r beta := by
      have hBLower : q.lambda ≤ correctionB q r beta := by
        unfold correctionB
        linarith [dispersion_nonneg r, dispersion_nonneg beta]
      exact hBLower.trans (le_add_of_nonneg_right
        (correctionSigma_nonneg (q := q) (kappa := 40) (by norm_num) hq.1 a r beta))
    have hgUpper : g beta ≤ q.lambda⁻¹ := by
      dsimp [g]
      exact (inv_le_inv₀ hdenPos hq.1).2 hdenLower
    rw [Real.norm_eq_abs, abs_of_nonneg (hgNonneg beta)]
    exact hgUpper
  change torusIntegral g ≤ 200000 / (r * Real.sqrt L)
  by_cases hg : Integrable g (volume.restrict torus)
  · by_cases hL : L < 16
    · let majorant : ℝ → ℝ := fun beta => 8 * (r ^ 2 + beta ^ 2)⁻¹
      have hmajorantCont : Continuous majorant := by
        dsimp [majorant]
        apply Continuous.mul continuous_const
        apply Continuous.inv₀
        · fun_prop
        · intro beta
          nlinarith [sq_pos_of_pos hrPos, sq_nonneg beta]
      have hmajorantInt : Integrable majorant (volume.restrict torus) :=
        by
          have hi : IntegrableOn majorant (Set.Icc (-Real.pi) Real.pi) :=
            hmajorantCont.continuousOn.integrableOn_Icc
          simpa only [torus, Measure.restrict_congr_set Ioc_ae_eq_Icc] using hi
      have hpoint : ∀ beta ∈ torus, g beta ≤ majorant beta := by
        intro beta hbeta
        have hbase := correctionB_quadratic_lower hq ha hr hbeta
        have hsigma := correctionSigma_nonneg (q := q) (kappa := 40)
          (by norm_num) hq.1 a r beta
        have hlower : (1 / 8 : ℝ) * (r ^ 2 + beta ^ 2) ≤
            correctionB q r beta + correctionSigma 40 q a r beta := by
          nlinarith [hq.1]
        have hleftPos : 0 < (1 / 8 : ℝ) * (r ^ 2 + beta ^ 2) := by
          positivity
        have hdenPos := correctionDenominator_pos (q := q) (kappa := 40)
          (by norm_num) hq.1 a r beta
        have hinv := (inv_le_inv₀ hdenPos hleftPos).2 hlower
        dsimp [g, majorant]
        calc
          (correctionB q r beta + correctionSigma 40 q a r beta)⁻¹ ≤
              ((1 / 8 : ℝ) * (r ^ 2 + beta ^ 2))⁻¹ := hinv
          _ = 8 * (r ^ 2 + beta ^ 2)⁻¹ := by field_simp
      have htorus : torusIntegral g ≤ torusIntegral majorant := by
        rw [torusIntegral, torusIntegral]
        simp only [smul_eq_mul]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply integral_mono_ae hg hmajorantInt
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with beta hbeta
        exact hpoint beta hbeta
      have hmajorantEval : torusIntegral majorant ≤ 8 / r := by
        have hcauchy := torusIntegral_cauchy_le hrPos (by norm_num : (0 : ℝ) < 1)
        have hscale : torusIntegral majorant =
            8 * torusIntegral (fun beta : ℝ => (r ^ 2 + beta ^ 2)⁻¹) := by
          exact torusIntegral_const_mul 8 _
        rw [hscale]
        calc
          8 * torusIntegral (fun beta : ℝ => (r ^ 2 + beta ^ 2)⁻¹) =
              8 * torusIntegral (fun beta : ℝ => (r ^ 2 + 1 ^ 2 * beta ^ 2)⁻¹) := by
                simp
          _ ≤ 8 * (1 / (r * 1)) := by exact mul_le_mul_of_nonneg_left hcauchy (by norm_num)
          _ = 8 / r := by ring
      have hsqrtLt : Real.sqrt L < 4 :=
        (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 4)).2 (by nlinarith)
      apply htorus.trans (hmajorantEval.trans ?_)
      rw [div_le_div_iff₀ hrPos hrightPos]
      nlinarith [hsqrtLPos]
    · have hLlarge : 16 ≤ L := le_of_not_gt hL
      let s : ℝ := r * Real.sqrt L
      let D : ℝ := Real.sqrt L / 2
      let c : ℝ := 1 / (4000 * Real.pi)
      let first : ℝ → ℝ := fun beta => c⁻¹ * (r ^ 2 + D ^ 2 * beta ^ 2)⁻¹
      let second : ℝ → ℝ := fun beta => 2 * c⁻¹ * (s ^ 2 + beta ^ 2)⁻¹
      let majorant : ℝ → ℝ := fun beta => first beta + second beta
      have hcPos : 0 < c := by dsimp [c]; positivity
      have hDPos : 0 < D := by dsimp [D]; positivity
      have hsPos : 0 < s := by dsimp [s]; positivity
      have hsqrtSq : (Real.sqrt L) ^ 2 = L := Real.sq_sqrt hLPos.le
      have hsqrtQuarter : Real.sqrt L ≤ L / 4 := by
        have hfour : 4 ≤ Real.sqrt L :=
          (Real.le_sqrt' (by norm_num : (0 : ℝ) < 4)).2 (by norm_num at hLlarge ⊢; exact hLlarge)
        nlinarith
      have hfirstCont : Continuous first := by
        dsimp [first]
        apply Continuous.mul continuous_const
        apply Continuous.inv₀
        · fun_prop
        · intro beta
          nlinarith [sq_pos_of_pos hrPos, sq_nonneg beta, sq_nonneg D]
      have hsecondCont : Continuous second := by
        dsimp [second]
        apply Continuous.mul continuous_const
        apply Continuous.inv₀
        · fun_prop
        · intro beta
          nlinarith [sq_pos_of_pos hsPos, sq_nonneg beta]
      have hfirstInt : Integrable first (volume.restrict torus) :=
        by
          have hi : IntegrableOn first (Set.Icc (-Real.pi) Real.pi) :=
            hfirstCont.continuousOn.integrableOn_Icc
          simpa only [torus, Measure.restrict_congr_set Ioc_ae_eq_Icc] using hi
      have hsecondInt : Integrable second (volume.restrict torus) :=
        by
          have hi : IntegrableOn second (Set.Icc (-Real.pi) Real.pi) :=
            hsecondCont.continuousOn.integrableOn_Icc
          simpa only [torus, Measure.restrict_congr_set Ioc_ae_eq_Icc] using hi
      have hmajorantInt : Integrable majorant (volume.restrict torus) :=
        hfirstInt.add hsecondInt
      have hpoint : ∀ beta ∈ torus, g beta ≤ majorant beta := by
        intro beta hbeta
        have hden := denominatorBound_proved hq ha r hr beta hbeta
        have hdenPos := correctionDenominator_pos (q := q) (kappa := 40)
          (by norm_num) hq.1 a r beta
        by_cases hinner : |beta| ≤ s
        · have habsDiv : |beta| / r ≤ Real.sqrt L := by
            apply (div_le_iff₀ hrPos).2
            simpa only [s, mul_comm] using hinner
          have hquotPos : 0 < (r + |beta|) / r := by positivity
          have hlogGrowth : Real.log ((r + |beta|) / r) ≤ |beta| / r := by
            calc
              Real.log ((r + |beta|) / r) ≤ (r + |beta|) / r - 1 :=
                Real.log_le_sub_one_of_pos hquotPos
              _ = |beta| / r := by field_simp [hrPos.ne']; ring
          have hlogDecomp : Real.log (q.r0 / (r + |beta|)) =
              Real.log (q.r0 / r) - Real.log ((r + |beta|) / r) := by
            rw [Real.log_div hr0Pos.ne' (add_pos_of_pos_of_nonneg hrPos (abs_nonneg _)).ne',
              Real.log_div hr0Pos.ne' hrPos.ne',
              Real.log_div (add_pos_of_pos_of_nonneg hrPos (abs_nonneg _)).ne' hrPos.ne']
            ring
          have hrawLog : L / 2 ≤ Real.log (q.r0 / (r + |beta|)) := by
            rw [hlogDecomp]
            dsimp [L]
            nlinarith
          have hlogFactor : L / 2 ≤ 1 + logPos (q.r0 / (r + |beta|)) := by
            calc
              L / 2 ≤ Real.log (q.r0 / (r + |beta|)) := hrawLog
              _ ≤ logPos (q.r0 / (r + |beta|)) := le_max_right _ _
              _ ≤ 1 + logPos (q.r0 / (r + |beta|)) :=
                le_add_of_nonneg_left zero_le_one
          have hcoreLower : c * (r ^ 2 + D ^ 2 * beta ^ 2) ≤
              correctionB q r beta + correctionSigma 40 q a r beta := by
            have hDsq : D ^ 2 = L / 4 := by
              dsimp [D]
              nlinarith
            have hinside : r ^ 2 + D ^ 2 * beta ^ 2 ≤
                q.lambda + r ^ 2 + beta ^ 2 *
                  (1 + logPos (q.r0 / (r + |beta|))) := by
              rw [hDsq]
              nlinarith [sq_nonneg beta, hq.1]
            exact (mul_le_mul_of_nonneg_left hinside hcPos.le).trans (by simpa [c] using hden)
          have hcorePos : 0 < c * (r ^ 2 + D ^ 2 * beta ^ 2) := by positivity
          have hinv := (inv_le_inv₀ hdenPos hcorePos).2 hcoreLower
          dsimp [g, majorant, first, second]
          calc
            (correctionB q r beta + correctionSigma 40 q a r beta)⁻¹ ≤
                (c * (r ^ 2 + D ^ 2 * beta ^ 2))⁻¹ := hinv
            _ = c⁻¹ * (r ^ 2 + D ^ 2 * beta ^ 2)⁻¹ := by
              rw [mul_inv_rev, mul_comm]
            _ ≤ c⁻¹ * (r ^ 2 + D ^ 2 * beta ^ 2)⁻¹ +
                2 * c⁻¹ * (s ^ 2 + beta ^ 2)⁻¹ := by
                  apply le_add_of_nonneg_right
                  exact mul_nonneg (mul_nonneg (by norm_num) (inv_pos.2 hcPos).le)
                    (inv_nonneg.2 (by positivity))
        · have hsAbs : s < |beta| := lt_of_not_ge hinner
          have hsBeta : s ^ 2 ≤ beta ^ 2 := by
            rw [← sq_abs beta]
            exact (sq_le_sq₀ hsPos.le (abs_nonneg beta)).2 hsAbs.le
          have houterLower : (c / 2) * (s ^ 2 + beta ^ 2) ≤
              correctionB q r beta + correctionSigma 40 q a r beta := by
            have hsimple : c * beta ^ 2 ≤
                correctionB q r beta + correctionSigma 40 q a r beta := by
              have hins : beta ^ 2 ≤ q.lambda + r ^ 2 + beta ^ 2 *
                  (1 + logPos (q.r0 / (r + |beta|))) := by
                have hfactor : 1 ≤ 1 + logPos (q.r0 / (r + |beta|)) := by
                  dsimp [logPos]
                  linarith [le_max_left 0 (Real.log (q.r0 / (r + |beta|)))]
                have hmul := mul_le_mul_of_nonneg_left hfactor (sq_nonneg beta)
                nlinarith [sq_nonneg r, hq.1]
              exact (mul_le_mul_of_nonneg_left hins hcPos.le).trans (by simpa [c] using hden)
            have hhalfLower : (c / 2) * (s ^ 2 + beta ^ 2) ≤ c * beta ^ 2 := by
              nlinarith [hcPos, hsBeta]
            exact hhalfLower.trans hsimple
          have houterPos : 0 < (c / 2) * (s ^ 2 + beta ^ 2) := by
            have hbetaSqPos : 0 < beta ^ 2 := by
              nlinarith [sq_pos_of_pos hsPos, hsBeta]
            positivity
          have hinv := (inv_le_inv₀ hdenPos houterPos).2 houterLower
          dsimp [g, majorant, first, second]
          calc
            (correctionB q r beta + correctionSigma 40 q a r beta)⁻¹ ≤
                ((c / 2) * (s ^ 2 + beta ^ 2))⁻¹ := hinv
            _ = 2 * c⁻¹ * (s ^ 2 + beta ^ 2)⁻¹ := by
              field_simp [hcPos.ne']
            _ ≤ c⁻¹ * (r ^ 2 + D ^ 2 * beta ^ 2)⁻¹ +
                2 * c⁻¹ * (s ^ 2 + beta ^ 2)⁻¹ := by
                  apply le_add_of_nonneg_left
                  exact mul_nonneg (inv_pos.2 hcPos).le (inv_nonneg.2 (by positivity))
      have htorus : torusIntegral g ≤ torusIntegral majorant := by
        rw [torusIntegral, torusIntegral]
        simp only [smul_eq_mul]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply integral_mono_ae hg hmajorantInt
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with beta hbeta
        exact hpoint beta hbeta
      have hmajorantEval : torusIntegral majorant ≤
          c⁻¹ * (1 / (r * D)) + 2 * c⁻¹ * (1 / (s * 1)) := by
        have hfirstCauchy := torusIntegral_cauchy_le hrPos hDPos
        have hsecondCauchy := torusIntegral_cauchy_le hsPos (by norm_num : (0 : ℝ) < 1)
        have hsplit : torusIntegral majorant = torusIntegral first + torusIntegral second := by
          exact torusIntegral_add_of_integrable hfirstInt hsecondInt
        rw [hsplit]
        have hfirstEval : torusIntegral first =
            c⁻¹ * torusIntegral (fun beta : ℝ => (r ^ 2 + D ^ 2 * beta ^ 2)⁻¹) := by
          exact torusIntegral_const_mul c⁻¹ _
        have hsecondEval : torusIntegral second =
            2 * c⁻¹ * torusIntegral (fun beta : ℝ => (s ^ 2 + 1 ^ 2 * beta ^ 2)⁻¹) := by
          simpa only [one_pow, one_mul] using torusIntegral_const_mul (2 * c⁻¹)
            (fun beta : ℝ => (s ^ 2 + beta ^ 2)⁻¹)
        rw [hfirstEval, hsecondEval]
        gcongr
      apply htorus.trans (hmajorantEval.trans ?_)
      have hcInv : c⁻¹ = 4000 * Real.pi := by
        dsimp [c]
        field_simp [Real.pi_ne_zero]
      have hD : D = Real.sqrt L / 2 := rfl
      have hs : s = r * Real.sqrt L := rfl
      rw [hcInv, hD, hs]
      field_simp [hrPos.ne', hsqrtLPos.ne', Real.pi_ne_zero]
      nlinarith [Real.pi_le_four, Real.pi_pos]
  · exact (hg hgProved).elim

/-- Complete provider for Proposition 4.2.  This is the declaration to seal as
`Manhattan.Frozen.Estimates.proposition_key`. -/
theorem propositionFiveTwoClaim_proved (K rho : ℝ) :
    PropositionFiveTwoClaim K rho := by
  intro hK hrhoPos hrho
  refine ⟨1 / (4000 * Real.pi), 200000, by positivity, by norm_num, ?_⟩
  intro lambda hlambda hlambdaOne a ha
  dsimp only
  let q : Parameters := ⟨lambda, K, rho⟩
  intro hsupport
  have hq : q.Admissible :=
    ⟨hlambda, hlambdaOne, hK, hrhoPos, hrho⟩
  have hdenominator := denominatorBound_proved hq ha
  have hbeta := betaIntegralBound_proved hq ha
  exact ⟨hdenominator, hbeta,
    propositionFiveTwoIntegralBound_of_betaIntegralBound
      hq (by norm_num) ha hsupport hbeta⟩

end

end Manhattan.Estimates
