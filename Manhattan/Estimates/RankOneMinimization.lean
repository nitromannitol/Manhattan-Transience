import Manhattan.Estimates.TargetStatements

/-!
# Rank-one quadratic minimization

This module proves (26)--(27) for the explicit admissible class in the
statement candidate.  The proof uses weighted Young's inequality for the
universal lower bound and checks both integrability conditions for the
displayed minimizer.

Paper: `manuscript.tex:962-980`.
-/

open MeasureTheory Set

namespace Manhattan.Estimates

noncomputable section

/-- Classical decidability, local to this file: the statements here are analytic, not computational. -/
local instance rankOnePropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

private theorem torusIntegral_if_mem {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : ℝ → E) {J : Set ℝ}
    (hJ : MeasurableSet J) :
    torusIntegral (fun x : ℝ => if x ∈ J then f x else 0) =
      (2 * Real.pi)⁻¹ • ∫ x in J ∩ torus, f x := by
  rw [torusIntegral]
  congr 1
  change ∫ x in torus, J.indicator f x = ∫ x in J ∩ torus, f x
  rw [integral_indicator hJ]
  rw [Measure.restrict_restrict hJ]

private theorem normalizedFactor_pos : 0 < (2 * Real.pi)⁻¹ := by positivity

private theorem rankOneSigma_nonneg (eta : ℂ) (M : ℝ → ℝ) (J : Set ℝ)
    (hJ : MeasurableSet J) (hM : ∀ alpha ∈ J ∩ torus, 0 < M alpha) :
    0 ≤ rankOneSigma eta M J := by
  rw [rankOneSigma, torusIntegral_if_mem _ hJ, smul_eq_mul]
  apply mul_nonneg (sq_nonneg _)
  apply mul_nonneg normalizedFactor_pos.le
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem (hJ.inter measurableSet_Ioc)] with alpha ha
  exact (inv_pos.2 (hM alpha ha)).le

private theorem rankOneMinimizer_admissible (B : ℝ) (M : ℝ → ℝ) (J : Set ℝ)
    (eta w : ℂ) (hB : 0 < B) (hJ : MeasurableSet J)
    (hM : ∀ alpha ∈ J ∩ torus, 0 < M alpha)
    (hInv : IntegrableOn (fun alpha : ℝ => (M alpha)⁻¹) (J ∩ torus)) :
    RankOneAdmissible M J (rankOneMinimizer B M J eta w) := by
  let S : Set ℝ := J ∩ torus
  have hS : MeasurableSet S := hJ.inter measurableSet_Ioc
  have hsigma : 0 ≤ rankOneSigma eta M J := rankOneSigma_nonneg eta M J hJ hM
  have hden : 0 < B + rankOneSigma eta M J := add_pos_of_pos_of_nonneg hB hsigma
  let c : ℂ := star eta * w / (B + rankOneSigma eta M J)
  have huEq : EqOn (rankOneMinimizer B M J eta w)
      (fun alpha : ℝ => (M alpha)⁻¹ • c) S := by
    intro alpha ha
    have hMne : M alpha ≠ 0 := (hM alpha ha).ne'
    simp only [rankOneMinimizer, if_pos ha.1, c]
    rw [Complex.real_smul, Complex.ofReal_inv]
    change star eta * w / ((M alpha : ℂ) * (B + rankOneSigma eta M J)) =
      ((M alpha)⁻¹ : ℂ) * (star eta * w / (B + rankOneSigma eta M J))
    field_simp [hMne, hden.ne']
  have huModel : IntegrableOn (fun alpha : ℝ => (M alpha)⁻¹ • c) S :=
    hInv.smul_const c
  have hu : IntegrableOn (rankOneMinimizer B M J eta w) S :=
    huModel.congr_fun huEq.symm hS
  refine ⟨hu, ?_⟩
  have henergyEq : EqOn
      (fun alpha : ℝ => M alpha * ‖rankOneMinimizer B M J eta w alpha‖ ^ 2)
      (fun alpha : ℝ => ‖c‖ ^ 2 * (M alpha)⁻¹) S := by
    intro alpha ha
    have hMpos := hM alpha ha
    change M alpha * ‖rankOneMinimizer B M J eta w alpha‖ ^ 2 = _
    rw [huEq ha]
    simp only [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hMpos]
    field_simp
  have henergyModel : IntegrableOn
      (fun alpha : ℝ => ‖c‖ ^ 2 * (M alpha)⁻¹) S := hInv.const_mul _
  exact henergyModel.congr_fun henergyEq.symm hS

private theorem weightedYoung (m d : ℝ) (eta w u : ℂ) (hm : 0 < m) (hd : 0 < d) :
    2 / d * (star w * (eta * u)).re -
        ‖eta‖ ^ 2 * ‖w‖ ^ 2 / (m * d ^ 2) ≤ m * ‖u‖ ^ 2 := by
  have hsq : 0 ≤ m * ‖u - star eta * w / (m * d)‖ ^ 2 :=
    mul_nonneg hm.le (sq_nonneg _)
  rw [← sub_nonneg]
  convert hsq using 1
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im, map_mul,
    Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, add_zero, zero_mul, sub_zero]
  field_simp [hm.ne', hd.ne']
  ring

private theorem rankOneScalarLower (B sigma : ℝ) (w y : ℂ)
    (hB : 0 < B) (hsigma : 0 ≤ sigma) :
    ‖w‖ ^ 2 / (B + sigma) ≤
      2 / (B + sigma) * (star w * y).re -
        sigma * ‖w‖ ^ 2 / (B + sigma) ^ 2 + B⁻¹ * ‖w - y‖ ^ 2 := by
  have hden : 0 < B + sigma := add_pos_of_pos_of_nonneg hB hsigma
  have hsq : 0 ≤ B⁻¹ * ‖y - (sigma / (B + sigma)) • w‖ ^ 2 :=
    mul_nonneg (inv_nonneg.2 hB.le) (sq_nonneg _)
  rw [← sub_nonneg]
  convert hsq using 1
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re,
    Complex.conj_im, Complex.real_smul, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero]
  field_simp [hB.ne', hden.ne']
  ring

/-- Equations (26)--(27): the explicit minimizer is admissible, attains the
claimed value, and no admissible complex function has lower energy. -/
theorem rankOneMinimizationClaim_proved : RankOneMinimizationClaim := by
  intro B M J eta w hB hJ hM hInv
  have hmin := rankOneMinimizer_admissible B M J eta w hB hJ hM hInv
  let S : Set ℝ := J ∩ torus
  have hS : MeasurableSet S := hJ.inter measurableSet_Ioc
  have hsigma : 0 ≤ rankOneSigma eta M J := rankOneSigma_nonneg eta M J hJ hM
  have hden : 0 < B + rankOneSigma eta M J := add_pos_of_pos_of_nonneg hB hsigma
  let c : ℂ := star eta * w / (B + rankOneSigma eta M J)
  let I : ℝ := torusIntegral (fun alpha : ℝ => if alpha ∈ J then (M alpha)⁻¹ else 0)
  have hsigmaEq : rankOneSigma eta M J = ‖eta‖ ^ 2 * I := rfl
  have huEq : EqOn (rankOneMinimizer B M J eta w)
      (fun alpha : ℝ => (M alpha)⁻¹ • c) S := by
    intro alpha ha
    have hMne : M alpha ≠ 0 := (hM alpha ha).ne'
    simp only [rankOneMinimizer, if_pos ha.1, c]
    rw [Complex.real_smul, Complex.ofReal_inv]
    change star eta * w / ((M alpha : ℂ) * (B + rankOneSigma eta M J)) =
      ((M alpha)⁻¹ : ℂ) * (star eta * w / (B + rankOneSigma eta M J))
    field_simp [hMne, hden.ne']
  have huIntegral : torusIntegral (fun alpha : ℝ =>
      if alpha ∈ J then rankOneMinimizer B M J eta w alpha else 0) = I • c := by
    rw [torusIntegral_if_mem _ hJ, setIntegral_congr_fun hS huEq]
    rw [integral_smul_const]
    simp only [torusIntegral_if_mem _ hJ, I, S, smul_smul, smul_eq_mul]
  have henergyEq : EqOn
      (fun alpha : ℝ => M alpha * ‖rankOneMinimizer B M J eta w alpha‖ ^ 2)
      (fun alpha : ℝ => ‖c‖ ^ 2 * (M alpha)⁻¹) S := by
    intro alpha ha
    have hMpos := hM alpha ha
    change M alpha * ‖rankOneMinimizer B M J eta w alpha‖ ^ 2 = _
    rw [huEq ha]
    simp only [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hMpos]
    field_simp
  have hweightedIntegral : torusIntegral (fun alpha : ℝ =>
      if alpha ∈ J then M alpha * ‖rankOneMinimizer B M J eta w alpha‖ ^ 2 else 0) =
      ‖c‖ ^ 2 * I := by
    rw [torusIntegral_if_mem _ hJ, setIntegral_congr_fun hS henergyEq]
    rw [integral_const_mul]
    simp only [torusIntegral_if_mem _ hJ, I, smul_eq_mul]
    ring
  refine ⟨hmin, ?_, ?_⟩
  · rw [rankOneEnergy, hweightedIntegral, huIntegral]
    have hcNorm : ‖c‖ ^ 2 = ‖eta‖ ^ 2 * ‖w‖ ^ 2 /
        (B + rankOneSigma eta M J) ^ 2 := by
      dsimp [c]
      rw [norm_div, norm_mul]
      have hnormStar : ‖(starRingEnd ℂ) eta‖ = ‖eta‖ := norm_star eta
      rw [hnormStar]
      rw [show ‖(B : ℂ) + (rankOneSigma eta M J : ℂ)‖ =
          B + rankOneSigma eta M J by
        rw [← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hden]]
      field_simp [hden.ne']
    have hresidual : w - eta * (I • c) =
        (B / (B + rankOneSigma eta M J)) • w := by
      have heta : eta * star eta = (‖eta‖ ^ 2 : ℝ) := by
        simpa only [Complex.normSq_eq_norm_sq] using Complex.mul_conj eta
      simp only [Complex.real_smul]
      push_cast
      simp only [c]
      have hdenC : (B : ℂ) + (rankOneSigma eta M J : ℂ) ≠ 0 := by
        rw [← Complex.ofReal_add]
        exact Complex.ofReal_ne_zero.mpr hden.ne'
      have hdenC' : ((rankOneSigma eta M J : ℂ) + B) ≠ 0 := by
        rw [add_comm]
        exact hdenC
      calc
        w - eta * ((I : ℂ) * (star eta * w /
            (B + rankOneSigma eta M J))) =
            w - (I : ℂ) * (eta * star eta) * w /
              (B + rankOneSigma eta M J) := by ring
        _ = w - ((‖eta‖ ^ 2 * I : ℝ) : ℂ) * w /
              (B + rankOneSigma eta M J) := by rw [heta]; push_cast; ring
        _ = (B : ℂ) / (B + rankOneSigma eta M J) * w := by
          rw [← hsigmaEq]
          field_simp [hdenC, hdenC']
          ring
    have hweightedConst :
        (‖eta‖ ^ 2 * ‖w‖ ^ 2 / (B + rankOneSigma eta M J) ^ 2) * I =
          rankOneSigma eta M J * ‖w‖ ^ 2 / (B + rankOneSigma eta M J) ^ 2 := by
      rw [hsigmaEq]
      ring
    rw [hcNorm, hresidual, norm_smul, Real.norm_eq_abs, abs_of_pos
      (div_pos hB hden)]
    rw [hweightedConst]
    field_simp [hB.ne', hden.ne']
    ring
  · intro u hu
    let uI : ℂ := torusIntegral (fun alpha : ℝ => if alpha ∈ J then u alpha else 0)
    let zfac : ℝ := (2 * Real.pi)⁻¹
    let low : ℝ → ℝ := fun alpha =>
      2 / (B + rankOneSigma eta M J) * (star w * (eta * u alpha)).re -
        ‖eta‖ ^ 2 * ‖w‖ ^ 2 /
          (M alpha * (B + rankOneSigma eta M J) ^ 2)
    have huSet : uI = zfac • ∫ alpha in S, u alpha := by
      dsimp [uI, zfac, S]
      rw [torusIntegral_if_mem _ hJ]
      rfl
    have hISet : I = zfac * ∫ alpha in S, (M alpha)⁻¹ := by
      dsimp [I, zfac, S]
      rw [torusIntegral_if_mem _ hJ]
      rfl
    have hcomplexInt : IntegrableOn (fun alpha : ℝ => star w * (eta * u alpha)) S :=
      (hu.1.const_mul eta).const_mul (star w)
    have hcrossSet : (∫ alpha in S, (star w * (eta * u alpha)).re) =
        (star w * (eta * ∫ alpha in S, u alpha)).re := by
      change (∫ alpha in S, RCLike.re (star w * (eta * u alpha))) = _
      rw [integral_re hcomplexInt, integral_const_mul, integral_const_mul]
      rw [RCLike.re_eq_complex_re]
    have hcrossInt : IntegrableOn (fun alpha : ℝ =>
        2 / (B + rankOneSigma eta M J) * (star w * (eta * u alpha)).re) S :=
      hcomplexInt.re.const_mul _
    have hinvInt : IntegrableOn (fun alpha : ℝ =>
        ‖eta‖ ^ 2 * ‖w‖ ^ 2 /
          (M alpha * (B + rankOneSigma eta M J) ^ 2)) S := by
      have heq : EqOn
          (fun alpha : ℝ => ‖eta‖ ^ 2 * ‖w‖ ^ 2 /
            (M alpha * (B + rankOneSigma eta M J) ^ 2))
          (fun alpha : ℝ =>
            (‖eta‖ ^ 2 * ‖w‖ ^ 2 / (B + rankOneSigma eta M J) ^ 2) *
              (M alpha)⁻¹) S := by
        intro alpha ha
        field_simp [(hM alpha ha).ne', hden.ne']
      have hmodel : IntegrableOn
          (fun alpha : ℝ =>
            (‖eta‖ ^ 2 * ‖w‖ ^ 2 / (B + rankOneSigma eta M J) ^ 2) *
              (M alpha)⁻¹) S := hInv.const_mul _
      exact hmodel.congr_fun heq.symm hS
    have hlowInt : IntegrableOn low S := hcrossInt.sub hinvInt
    have hpoint : ∀ᵐ alpha ∂volume.restrict S,
        low alpha ≤ M alpha * ‖u alpha‖ ^ 2 := by
      filter_upwards [ae_restrict_mem hS] with alpha ha
      exact weightedYoung (M alpha) (B + rankOneSigma eta M J) eta w (u alpha)
        (hM alpha ha) hden
    have hsetLower : (∫ alpha in S, low alpha) ≤
        ∫ alpha in S, M alpha * ‖u alpha‖ ^ 2 :=
      integral_mono_ae hlowInt hu.2 hpoint
    have htorusLower : torusIntegral (fun alpha : ℝ =>
        if alpha ∈ J then low alpha else 0) ≤
        torusIntegral (fun alpha : ℝ =>
          if alpha ∈ J then M alpha * ‖u alpha‖ ^ 2 else 0) := by
      rw [torusIntegral_if_mem _ hJ, torusIntegral_if_mem _ hJ]
      simp only [smul_eq_mul]
      exact mul_le_mul_of_nonneg_left hsetLower normalizedFactor_pos.le
    have hlowEval : torusIntegral (fun alpha : ℝ =>
        if alpha ∈ J then low alpha else 0) =
        2 / (B + rankOneSigma eta M J) * (star w * (eta * uI)).re -
          rankOneSigma eta M J * ‖w‖ ^ 2 /
            (B + rankOneSigma eta M J) ^ 2 := by
      rw [torusIntegral_if_mem _ hJ]
      simp only [low]
      rw [integral_sub hcrossInt hinvInt, integral_const_mul]
      have hinvRewrite :
          (∫ alpha in S, ‖eta‖ ^ 2 * ‖w‖ ^ 2 /
              (M alpha * (B + rankOneSigma eta M J) ^ 2)) =
            (‖eta‖ ^ 2 * ‖w‖ ^ 2 / (B + rankOneSigma eta M J) ^ 2) *
              ∫ alpha in S, (M alpha)⁻¹ := by
        calc
          _ = ∫ alpha in S,
              (‖eta‖ ^ 2 * ‖w‖ ^ 2 / (B + rankOneSigma eta M J) ^ 2) *
                (M alpha)⁻¹ := by
            apply setIntegral_congr_fun hS
            intro alpha ha
            field_simp [(hM alpha ha).ne', hden.ne']
          _ = _ := integral_const_mul _ _
      rw [hinvRewrite, hcrossSet]
      simp only [smul_eq_mul]
      rw [hsigmaEq, huSet, hISet]
      dsimp [zfac]
      ring
    rw [rankOneEnergy]
    exact (rankOneScalarLower B (rankOneSigma eta M J) w (eta * uI) hB hsigma).trans
      (by
        rw [← hlowEval]
        simpa only [uI] using add_le_add htorusLower (le_refl (B⁻¹ * ‖w - eta * uI‖ ^ 2)))

end

end Manhattan.Estimates
