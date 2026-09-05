import Manhattan.Glue.SummandsTorus
import Manhattan.Glue.TransportDischarge
import Manhattan.Glue.Summands

/-!
# The momentum bridge for the degree-three summand of (22)

`Manhattan/Glue/TransportDischarge.lean` bounds the
degree-three `H` quadratic form of the corrected coefficient `k_p` at the
*shifted* momentum `(0,-p₂)`, because `Manhattan.correctionType112Coefficients`
takes the Fourier coefficients of the manuscript's `k̃` in the shifted
variables `(r,r',β)` of `manuscript.tex:812-814` without the compensating
unimodular phase. Summand 2 of (22) is the same quadratic form at the actual
momentum `p`. This file bridges the two: the two symbols differ by the fixed
shift `(p₁, p₂+p₂)` of the total frequency, and `dispersion_add_le` turns that
into a universal comparison with an additive error `O(|p₁|²)‖k‖²`.

Paper: `manuscript.tex:743-751` ((Hsym)), `manuscript.tex:762-790` ((22)).
-/

noncomputable section

open MeasureTheory Set UnitAddTorus
open ComplexConjugate InnerProductSpace RCLike

namespace Manhattan.Glue

attribute [local instance] Real.fact_zero_lt_one

/-! ### The type-`112` symbol at a general momentum -/

/-- The total frequency of the type-`(1,1,2)` pattern at an arbitrary frozen
momentum is the manuscript's `(β, r+r'-p₂)` shifted by `(p₁, p₂+p₂)`, modulo
`2π` in each coordinate. -/
theorem symbolWeight_type112Pattern_shift (lam : ℝ) (p : Fin 2 → ℝ) (p₂ : ℝ)
    (t : UnitAddTorus (Fin 3)) :
    symbolWeight 3 lam p type112Pattern t =
      lam + Manhattan.Estimates.dispersion
            (rawCorrectionTotalFrequency p₂ t 0 + p 0) +
        Manhattan.Estimates.dispersion
          (rawCorrectionTotalFrequency p₂ t 1 + (p 1 + p₂)) := by
  obtain ⟨k0, hk0⟩ := two_pi_torusLift (t 0)
  obtain ⟨k1, hk1⟩ := two_pi_torusLift (t 1)
  obtain ⟨k2, hk2⟩ := two_pi_torusLift (t 2)
  rw [symbolWeight_def, Manhattan.Estimates.theta]
  have h0 : Manhattan.Estimates.dispersion
        (totalFrequency 3 p type112Pattern t 0) =
      Manhattan.Estimates.dispersion (rawCorrectionTotalFrequency p₂ t 0 + p 0) := by
    rw [totalFrequency_type112_zero]
    have hshift : p 0 + 2 * Real.pi * torusLift (t 2) =
        (rawCorrectionTotalFrequency p₂ t 0 + p 0) + k2 * (2 * Real.pi) := by
      rw [hk2]
      simp [rawCorrectionTotalFrequency, Manhattan.Estimates.mixedTotalFrequency]
      ring
    rw [hshift, dispersion_add_int_two_pi]
  have h1 : Manhattan.Estimates.dispersion
        (totalFrequency 3 p type112Pattern t 1) =
      Manhattan.Estimates.dispersion
        (rawCorrectionTotalFrequency p₂ t 1 + (p 1 + p₂)) := by
    rw [totalFrequency_type112_one]
    have hexp : 2 * Real.pi * (torusLift (t 0) + torusLift (t 1)) =
        2 * Real.pi * torusLift (t 0) + 2 * Real.pi * torusLift (t 1) := by ring
    have hshift : p 1 + 2 * Real.pi * (torusLift (t 0) + torusLift (t 1)) =
        (rawCorrectionTotalFrequency p₂ t 1 + (p 1 + p₂)) +
          ((k0 + k1 : ℤ) : ℝ) * (2 * Real.pi) := by
      rw [hexp, hk0, hk1]
      simp only [rawCorrectionTotalFrequency, Manhattan.Estimates.mixedTotalFrequency,
        Matrix.cons_val_one, Matrix.cons_val_fin_one]
      push_cast
      ring
    rw [hshift, dispersion_add_int_two_pi]
  rw [h0, h1]
  ring

/-- The comparison of the two symbols. -/
theorem symbolWeight_type112_le {lam : ℝ} (hlam : 0 ≤ lam) (p : Fin 2 → ℝ)
    (p₂ : ℝ) (t : UnitAddTorus (Fin 3)) :
    symbolWeight 3 lam p type112Pattern t ≤
      2 * symbolWeight 3 lam ![0, -p₂] type112Pattern t +
        (2 * Manhattan.Estimates.dispersion (p 0) +
          2 * Manhattan.Estimates.dispersion (p 1 + p₂)) := by
  rw [symbolWeight_type112Pattern_shift lam p p₂ t,
    symbolWeight_type112Pattern lam p₂ t, Manhattan.Estimates.theta]
  have h0 := dispersion_add_le (rawCorrectionTotalFrequency p₂ t 0) (p 0)
  have h1 := dispersion_add_le (rawCorrectionTotalFrequency p₂ t 1) (p 1 + p₂)
  linarith

/-- Measurability of the manuscript's total frequency. -/
theorem measurable_rawCorrectionTotalFrequency (p₂ : ℝ) (i : Fin 2) :
    Measurable (fun t : UnitAddTorus (Fin 3) =>
      rawCorrectionTotalFrequency p₂ t i) := by
  fin_cases i
  · change Measurable (fun t : UnitAddTorus (Fin 3) =>
      Manhattan.unitTorusAngle (t 2))
    exact Manhattan.unitTorusAngle_measurable.comp (measurable_pi_apply 2)
  · change Measurable (fun t : UnitAddTorus (Fin 3) =>
      Manhattan.unitTorusAngle (t 0) + Manhattan.unitTorusAngle (t 1) - p₂)
    have h0 : Measurable (fun t : UnitAddTorus (Fin 3) =>
        Manhattan.unitTorusAngle (t 0)) :=
      Manhattan.unitTorusAngle_measurable.comp (measurable_pi_apply 0)
    have h1 : Measurable (fun t : UnitAddTorus (Fin 3) =>
        Manhattan.unitTorusAngle (t 1)) :=
      Manhattan.unitTorusAngle_measurable.comp (measurable_pi_apply 1)
    exact (h0.add h1).sub_const p₂

theorem measurable_symbolWeight_type112 (lam : ℝ) (p : Fin 2 → ℝ) (p₂ : ℝ) :
    Measurable (fun t : UnitAddTorus (Fin 3) =>
      symbolWeight 3 lam p type112Pattern t) := by
  have h : (fun t : UnitAddTorus (Fin 3) => symbolWeight 3 lam p type112Pattern t) =
      fun t : UnitAddTorus (Fin 3) =>
        lam + Manhattan.Estimates.dispersion
              (rawCorrectionTotalFrequency p₂ t 0 + p 0) +
          Manhattan.Estimates.dispersion
            (rawCorrectionTotalFrequency p₂ t 1 + (p 1 + p₂)) :=
    funext fun t => symbolWeight_type112Pattern_shift lam p p₂ t
  rw [h]
  have m0 := measurable_rawCorrectionTotalFrequency p₂ 0
  have m1 := measurable_rawCorrectionTotalFrequency p₂ 1
  unfold Manhattan.Estimates.dispersion
  refine (measurable_const.add ?_).add ?_
  · exact measurable_const.sub
      (Real.continuous_cos.measurable.comp (m0.add_const (p 0)))
  · exact measurable_const.sub
      (Real.continuous_cos.measurable.comp (m1.add_const (p 1 + p₂)))

/-! ### The comparison of the two degree-three quadratic forms -/

theorem integrable_symbolWeight_mul {lam : ℝ} (hlam : 0 ≤ lam) (p : Fin 2 → ℝ)
    (p₂ : ℝ) (Psi : Lp ℂ 2 (LineTorusMeasure 3)) :
    Integrable (fun t : UnitAddTorus (Fin 3) =>
      symbolWeight 3 lam p type112Pattern t *
        ‖(Psi : UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2) (LineTorusMeasure 3) := by
  have hg : Integrable (fun t : UnitAddTorus (Fin 3) =>
      ‖(Psi : UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2) (LineTorusMeasure 3) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable Psi)).1 (Lp.memLp Psi)
  refine (hg.const_mul (lam + 4)).mono
    (((measurable_symbolWeight_type112 lam p p₂).aestronglyMeasurable).mul
      (hg.aestronglyMeasurable)) ?_
  filter_upwards with t
  have hWnn : 0 ≤ symbolWeight 3 lam p type112Pattern t :=
    le_trans hlam (symbolWeight_ge 3 lam p type112Pattern t)
  have hWle : symbolWeight 3 lam p type112Pattern t ≤ lam + 4 :=
    symbolWeight_le 3 lam p type112Pattern t
  have hgnn : (0 : ℝ) ≤ ‖(Psi : UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2 := sq_nonneg _
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hWnn hgnn),
    abs_of_nonneg (mul_nonneg (by linarith) hgnn)]
  exact mul_le_mul_of_nonneg_right hWle hgnn

/-- **The momentum bridge.** The degree-three `H` energy of a type-`(1,1,2)`
Walsh vector at the true momentum `p` is controlled by its energy at the
shifted momentum `(0,-p₂)`, with an
additive error proportional to `‖k‖²`. -/
theorem hThreeForm_type112_le {lam : ℝ} (hlam : 0 ≤ lam) (p : Fin 2 → ℝ)
    (p₂ : ℝ) (c : ℓ²(Manhattan.Type112Index, ℂ)) :
    hThreeForm lam p (Manhattan.type112WalshSynthesis c) ≤
      2 * hThreeForm lam ![0, -p₂] (Manhattan.type112WalshSynthesis c) +
        (2 * Manhattan.Estimates.dispersion (p 0) +
          2 * Manhattan.Estimates.dispersion (p 1 + p₂)) * ‖c‖ ^ 2 := by
  set Psi : Lp ℂ 2 (LineTorusMeasure 3) := type112FreqFun c with hPsi
  set g : UnitAddTorus (Fin 3) → ℝ :=
    fun t => ‖(Psi : UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2 with hgdef
  set K : ℝ := 2 * Manhattan.Estimates.dispersion (p 0) +
    2 * Manhattan.Estimates.dispersion (p 1 + p₂) with hK
  have hg : Integrable g (LineTorusMeasure 3) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable Psi)).1 (Lp.memLp Psi)
  have hgnn : ∀ t, 0 ≤ g t := fun t => sq_nonneg _
  have hgtotal : ∫ t, g t ∂(LineTorusMeasure 3) = ‖c‖ ^ 2 := by
    rw [hgdef, integral_norm_sq_lp, hPsi, type112FreqFun.norm_map]
  have hW := integrable_symbolWeight_mul hlam p p₂ Psi
  have hW' := integrable_symbolWeight_mul hlam ![0, -p₂] p₂ Psi
  rw [hThreeForm_type112WalshSynthesis, hThreeForm_type112WalshSynthesis]
  have hstep : ∫ t, symbolWeight 3 lam p type112Pattern t * g t
        ∂(LineTorusMeasure 3) ≤
      ∫ t, (2 * (symbolWeight 3 lam ![0, -p₂] type112Pattern t * g t) + K * g t)
        ∂(LineTorusMeasure 3) := by
    refine integral_mono hW ((hW'.const_mul 2).add (hg.const_mul K)) ?_
    intro t
    have hle := symbolWeight_type112_le hlam p p₂ t
    nlinarith [hgnn t, hle]
  refine hstep.trans_eq ?_
  rw [integral_add (hW'.const_mul 2) (hg.const_mul K), integral_const_mul,
    integral_const_mul, hgtotal]

/-! ### The `L²` mass of the correction is controlled by its multiplier energy -/

/-- If the manuscript's `k̃` does not vanish, one of the two `α`-intervals of
`manuscript.tex:1040-1063` contains `α = r+r'-p₂`. -/
theorem mem_correctionInterval_of_ne_zero {kappa : ℝ}
    {q : Manhattan.Estimates.Parameters} (a p₂ r r' beta : ℝ)
    (h : Manhattan.Estimates.correctionCoefficient kappa q a p₂ r r' beta ≠ 0) :
    (r + r' - p₂) ∈ Manhattan.Estimates.correctionInterval q a r beta ∨
      (r + r' - p₂) ∈ Manhattan.Estimates.correctionInterval q a r' beta := by
  classical
  by_contra hcon
  push_neg at hcon
  exact h (by simp [Manhattan.Estimates.correctionCoefficient, hcon.1, hcon.2])

/-- On either interval, `α` is separated from zero by `4K·a` and stays inside
`[-ρ,0]`. -/
theorem correctionInterval_bounds {q : Manhattan.Estimates.Parameters}
    (hK : 1 ≤ q.K) {a s beta alpha : ℝ} (ha : 0 ≤ a)
    (h : alpha ∈ Manhattan.Estimates.correctionInterval q a s beta) :
    alpha ≤ -(4 * q.K * a) ∧ -q.rho ≤ alpha := by
  classical
  unfold Manhattan.Estimates.correctionInterval at h
  by_cases hcond : s ∈ q.supportInterval a ∧
      s + q.delta a + |beta| ≤ q.rho / (8 * q.K)
  · rw [if_pos hcond] at h
    obtain ⟨hlow, hhigh⟩ := h
    have hdelta : a ≤ q.delta a := by
      rw [Manhattan.Estimates.Parameters.delta]
      have := Real.sqrt_nonneg q.lambda
      linarith
    have hdeltaNonneg : 0 ≤ q.delta a := le_trans ha hdelta
    have hs : q.K * q.delta a ≤ s := hcond.1.1
    have hsNonneg : 0 ≤ s := le_trans (by positivity) hs
    have hbeta : 0 ≤ |beta| := abs_nonneg beta
    refine ⟨hhigh.trans ?_, hlow⟩
    have : 4 * q.K * a ≤ 4 * q.K * (s + q.delta a + |beta|) := by
      have hKpos : (0 : ℝ) ≤ 4 * q.K := by linarith
      have : a ≤ s + q.delta a + |beta| := by linarith
      exact mul_le_mul_of_nonneg_left this hKpos
    linarith
  · rw [if_neg hcond] at h
    exact absurd h (Set.notMem_empty _)

/-- **The frequency separation.** Wherever the manuscript's `k̃` is nonzero,
the multiplier of (28) dominates `a²`. This is the quantitative form of
`manuscript.tex:1040-1063`: the two `α`-intervals sit at distance at least
`4Kδ ≥ 4Ka` from the origin. -/
theorem sq_le_multiplier_of_ne_zero {q : Manhattan.Estimates.Parameters}
    (hK : 1 ≤ q.K) (hlam : 0 ≤ q.lambda) (hrho : q.rho ≤ Real.pi) {a p₂ : ℝ}
    (ha : 0 ≤ a) {x : UnitAddTorus (Fin 3)}
    (hnz : Manhattan.rawCorrectionFunction 40 q a p₂ x ≠ 0) :
    a ^ 2 ≤ Manhattan.Estimates.multiplier 40 q
      (rawCorrectionTotalFrequency p₂ x) := by
  set r : ℝ := Manhattan.unitTorusAngle (x 0) with hr
  set r' : ℝ := Manhattan.unitTorusAngle (x 1) with hr'
  set beta : ℝ := Manhattan.unitTorusAngle (x 2) with hbeta
  set alpha : ℝ := r + r' - p₂ with halphaDef
  have hP1 : rawCorrectionTotalFrequency p₂ x 1 = alpha := by
    simp [rawCorrectionTotalFrequency, Manhattan.Estimates.mixedTotalFrequency,
      halphaDef, hr, hr']
  have hmem := mem_correctionInterval_of_ne_zero (kappa := 40) a p₂ r r' beta hnz
  have hbounds : alpha ≤ -(4 * q.K * a) ∧ -q.rho ≤ alpha := by
    rcases hmem with hm | hm
    · exact correctionInterval_bounds hK ha hm
    · exact correctionInterval_bounds hK ha hm
  have hKa : 0 ≤ 4 * q.K * a := by positivity
  have hnp : alpha ≤ 0 := by linarith [hbounds.1]
  have habs : 4 * q.K * a ≤ |alpha| := by
    rw [abs_of_nonpos hnp]
    linarith [hbounds.1]
  have habsPi : |alpha| ≤ Real.pi := by
    rw [abs_of_nonpos hnp]
    linarith [hbounds.2]
  have hdisp := (Manhattan.Estimates.dispersion_quadratic_bounds habsPi).1
  have hd0 : 0 ≤ Manhattan.Estimates.dispersion alpha :=
    Manhattan.Estimates.dispersion_nonneg alpha
  have hsq : (4 * q.K * a) ^ 2 ≤ alpha ^ 2 := by
    have h := mul_self_le_mul_self hKa habs
    rw [← sq, ← sq, sq_abs] at h
    exact h
  have hKsq : (1 : ℝ) ≤ q.K ^ 2 := by nlinarith [hK]
  have halpha16 : 16 * a ^ 2 ≤ alpha ^ 2 := by
    have h1 : 16 * a ^ 2 ≤ (4 * q.K * a) ^ 2 := by
      nlinarith [hKsq, sq_nonneg a]
    linarith [hsq]
  have hpiPos : (0 : ℝ) < Real.pi ^ 2 := by positivity
  have hpi2 : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_le_four, Real.pi_pos]
  have hmul : 2 * alpha ^ 2 ≤ Manhattan.Estimates.dispersion alpha * Real.pi ^ 2 := by
    rw [div_le_iff₀ hpiPos] at hdisp
    linarith
  have hdlow : 2 * a ^ 2 ≤ Manhattan.Estimates.dispersion alpha := by
    nlinarith [hmul, hpi2, hd0, halpha16]
  have hd1 : 0 ≤ Manhattan.Estimates.dispersion
      (rawCorrectionTotalFrequency p₂ x 0) :=
    Manhattan.Estimates.dispersion_nonneg _
  have hs1 : 0 ≤ |Real.sin (rawCorrectionTotalFrequency p₂ x 0 / 2)| := abs_nonneg _
  have hs2 : 0 ≤ |Real.sin (alpha / 2)| := abs_nonneg _
  unfold Manhattan.Estimates.multiplier Manhattan.Estimates.theta
  rw [hP1]
  nlinarith [hdlow, hd1, hs1, hs2, hlam, sq_nonneg a]

end Manhattan.Glue

namespace Manhattan.Glue

attribute [local instance] cubicUnitAddCircleMeasureSpace

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The `L²` mass of the manuscript's `k̃`, weighted by `a²`, is dominated by
its multiplier energy. -/
theorem sq_mul_integral_le_rawCubicMultiplierEnergy
    {q : Manhattan.Estimates.Parameters} (hlambda : 0 < q.lambda) (hK : 1 ≤ q.K)
    (hrho : q.rho ≤ Real.pi) {a p₂ : ℝ} (ha : 0 ≤ a) :
    a ^ 2 * ∫ x : UnitAddTorus (Fin 3),
        ‖Manhattan.rawCorrectionFunction 40 q a p₂ x‖ ^ 2 ≤
      rawCubicMultiplierEnergy q a p₂ := by
  classical
  have hmeasf : Measurable (fun x : UnitAddTorus (Fin 3) =>
      ‖Manhattan.rawCorrectionFunction 40 q a p₂ x‖ ^ 2) :=
    (Manhattan.rawCorrectionFunction_measurable 40 q a p₂).norm.pow_const 2
  have hbound : ∀ x : UnitAddTorus (Fin 3),
      ‖Manhattan.rawCorrectionFunction 40 q a p₂ x‖ ^ 2 ≤
        ((40 * q.lambda)⁻¹ * (2 * q.lambda⁻¹)) ^ 2 :=
    fun x => norm_rawCorrectionFunction_sq_le hlambda a p₂ x
  have hmeasM : Measurable (fun x : UnitAddTorus (Fin 3) =>
      Manhattan.Estimates.multiplier 40 q (rawCorrectionTotalFrequency p₂ x)) := by
    have m0 := measurable_rawCorrectionTotalFrequency p₂ 0
    have m1 := measurable_rawCorrectionTotalFrequency p₂ 1
    unfold Manhattan.Estimates.multiplier Manhattan.Estimates.theta
      Manhattan.Estimates.dispersion
    refine measurable_const.mul ?_
    refine ((measurable_const.add ?_).add ?_).add ?_
    · exact (measurable_const.sub
        (Real.continuous_cos.measurable.comp m0)).add
        (measurable_const.sub (Real.continuous_cos.measurable.comp m1))
    · exact measurable_const.mul
        ((continuous_abs.comp Real.continuous_sin).measurable.comp (m0.div_const 2))
    · exact measurable_const.mul
        ((continuous_abs.comp Real.continuous_sin).measurable.comp (m1.div_const 2))
  have hMbound : ∀ x : UnitAddTorus (Fin 3),
      Manhattan.Estimates.multiplier 40 q (rawCorrectionTotalFrequency p₂ x) ≤
        40 * (q.lambda + 8) := by
    intro x
    unfold Manhattan.Estimates.multiplier Manhattan.Estimates.theta
      Manhattan.Estimates.dispersion
    have h0 := Real.neg_one_le_cos (rawCorrectionTotalFrequency p₂ x 0)
    have h1 := Real.neg_one_le_cos (rawCorrectionTotalFrequency p₂ x 1)
    have hs0 : |Real.sin (rawCorrectionTotalFrequency p₂ x 0 / 2)| ≤ 1 :=
      Real.abs_sin_le_one _
    have hs1 : |Real.sin (rawCorrectionTotalFrequency p₂ x 1 / 2)| ≤ 1 :=
      Real.abs_sin_le_one _
    nlinarith [h0, h1, hs0, hs1]
  have hMnonneg : ∀ x : UnitAddTorus (Fin 3),
      0 ≤ Manhattan.Estimates.multiplier 40 q (rawCorrectionTotalFrequency p₂ x) :=
    fun x => Manhattan.Estimates.multiplier_nonneg (by norm_num) hlambda.le _
  have hIntf : Integrable (fun x : UnitAddTorus (Fin 3) =>
      ‖Manhattan.rawCorrectionFunction 40 q a p₂ x‖ ^ 2) := by
    refine Integrable.of_bound hmeasf.aestronglyMeasurable
      (((40 * q.lambda)⁻¹ * (2 * q.lambda⁻¹)) ^ 2) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hbound x
  have hIntM : Integrable (fun x : UnitAddTorus (Fin 3) =>
      Manhattan.Estimates.multiplier 40 q (rawCorrectionTotalFrequency p₂ x) *
        ‖Manhattan.rawCorrectionFunction 40 q a p₂ x‖ ^ 2) := by
    refine Integrable.of_bound (hmeasM.mul hmeasf).aestronglyMeasurable
      ((40 * (q.lambda + 8)) * ((40 * q.lambda)⁻¹ * (2 * q.lambda⁻¹)) ^ 2) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hMnonneg x) (sq_nonneg _))]
    exact mul_le_mul (hMbound x) (hbound x) (sq_nonneg _)
      (by positivity)
  have hpoint : ∀ x : UnitAddTorus (Fin 3),
      a ^ 2 * ‖Manhattan.rawCorrectionFunction 40 q a p₂ x‖ ^ 2 ≤
        Manhattan.Estimates.multiplier 40 q (rawCorrectionTotalFrequency p₂ x) *
          ‖Manhattan.rawCorrectionFunction 40 q a p₂ x‖ ^ 2 := by
    intro x
    by_cases hz : Manhattan.rawCorrectionFunction 40 q a p₂ x = 0
    · simp [hz]
    · exact mul_le_mul_of_nonneg_right
        (sq_le_multiplier_of_ne_zero hK hlambda.le hrho ha hz) (sq_nonneg _)
  rw [rawCubicMultiplierEnergy, ← integral_const_mul]
  exact integral_mono (hIntf.const_mul _) hIntM hpoint

/-- The projected type-`112` coefficient has `L²` mass at most that of the raw
correction. -/
theorem sq_norm_correctionType112Coefficients_le
    {q : Manhattan.Estimates.Parameters} (hlambda : 0 < q.lambda) (a p₂ : ℝ) :
    ‖Manhattan.correctionType112Coefficients (kappa := 40) (by norm_num)
        hlambda a p₂‖ ^ 2 ≤
      ∫ x : UnitAddTorus (Fin 3),
        ‖Manhattan.rawCorrectionFunction 40 q a p₂ x‖ ^ 2 := by
  have h1 := Manhattan.norm_correctionType112Coefficients_le
    (kappa := 40) (by norm_num) hlambda a p₂
  have h2 : ‖Manhattan.rawCorrectionFourierCoefficients (kappa := 40)
        (by norm_num) hlambda a p₂‖ =
      ‖Manhattan.rawCorrectionL2 (kappa := 40) (by norm_num) hlambda a p₂‖ := by
    rw [Manhattan.rawCorrectionFourierCoefficients]
    exact LinearIsometryEquiv.norm_map _ _
  have h3 : ‖Manhattan.rawCorrectionL2 (kappa := 40) (by norm_num)
        hlambda a p₂‖ ^ 2 =
      ∫ x : UnitAddTorus (Fin 3),
        ‖Manhattan.rawCorrectionFunction 40 q a p₂ x‖ ^ 2 := by
    rw [← integral_norm_sq_lp]
    refine integral_congr_ae ?_
    filter_upwards [(Manhattan.rawCorrectionFunction_memLp (kappa := 40)
      (by norm_num) hlambda a p₂).coeFn_toLp] with x hx
    have hx' : (Manhattan.rawCorrectionL2 (kappa := 40) (by norm_num)
        hlambda a p₂ : UnitAddTorus (Fin 3) → ℂ) x =
        Manhattan.rawCorrectionFunction 40 q a p₂ x := hx
    rw [hx']
  rw [← h3]
  exact pow_le_pow_left₀ (norm_nonneg _) (h1.trans_eq h2) 2

/-- The raw `H`-weight energy is at most the whole scalar core of Lemma 5.2. -/
theorem rawCubicHWeightEnergy_le_core {q : Manhattan.Estimates.Parameters}
    (hlambda : 0 < q.lambda) (a p₂ : ℝ) :
    rawCubicHWeightEnergy q a p₂ ≤ rawCubicCoreEnergy q a p₂ := by
  have hraise : 0 ≤ rawCubicRaisingEnergy q a p₂ := by
    rw [rawCubicRaisingEnergy]
    refine integral_nonneg fun x => ?_
    have h1 : 0 ≤ Real.sin (rawCorrectionTotalFrequency p₂ x 0) ^ 2 /
        Real.sqrt (q.lambda +
          Manhattan.Estimates.dispersion (rawCorrectionTotalFrequency p₂ x 0)) :=
      div_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)
    have h2 : 0 ≤ Real.sin (rawCorrectionTotalFrequency p₂ x 1) ^ 2 /
        Real.sqrt (q.lambda +
          Manhattan.Estimates.dispersion (rawCorrectionTotalFrequency p₂ x 1)) :=
      div_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)
    exact mul_nonneg (by linarith) (sq_nonneg _)
  linarith [rawCubicCoreEnergy_eq_add hlambda a p₂, hraise]

/-- **Summand 2 of (22) for the concrete correction.** The degree-three `H`
energy of `k_p` at the true momentum `p` is `≤ 14 C √L`.

the (shift) phase installed (E-009)
lets summand 2 be discharged at `2 C √L` through
`Manhattan.Glue.hThreeForm_type112ShiftTwist_frozen`, so nothing consumes this
weaker unshifted bound any more. -/
theorem hThreeForm_correctionWalsh_le {q : Manhattan.Estimates.Parameters}
    (hlambda : 0 < q.lambda) (hK : 1 ≤ q.K) (hrho : 0 ≤ q.rho)
    (hrhopi : 3 * q.rho < Real.pi) {C : ℝ} (p : Fin 2 → ℝ)
    (horder : |p 1| ≤ |p 0|)
    (hfive : Manhattan.Estimates.PropositionFiveTwoIntegralBound 40 C q |p 0|) :
    hThreeForm q.lambda p
        (Manhattan.correctionWalsh (kappa := 40) (by norm_num) hlambda
          |p 0| (p 1)) ≤
      14 * C * Real.sqrt (q.scaleLog |p 0|) := by
  have ha : (0 : ℝ) ≤ |p 0| := abs_nonneg _
  have hrhopiLe : q.rho ≤ Real.pi := by linarith
  set c := Manhattan.correctionType112Coefficients (kappa := 40) (by norm_num)
    hlambda |p 0| (p 1) with hc
  have hk : Manhattan.correctionWalsh (kappa := 40) (by norm_num) hlambda
      |p 0| (p 1) = Manhattan.type112WalshSynthesis c := rfl
  have hbridge := hThreeForm_type112_le hlambda.le p (p 1) c
  have hshift : hThreeForm q.lambda ![0, -(p 1)]
      (Manhattan.type112WalshSynthesis c) ≤ rawCubicHWeightEnergy q |p 0| (p 1) :=
    hThreeForm_frozen_correctionWalsh_le hlambda |p 0| (p 1)
  have hcore : rawCubicHWeightEnergy q |p 0| (p 1) ≤
      2 * C * Real.sqrt (q.scaleLog |p 0|) :=
    (rawCubicHWeightEnergy_le_core hlambda |p 0| (p 1)).trans
      (rawCubicCoreEnergy_le_sqrtScale hlambda hK hrho hrhopi ha horder hfive)
  have hmass : |p 0| ^ 2 * ‖c‖ ^ 2 ≤ 2 * C * Real.sqrt (q.scaleLog |p 0|) := by
    refine le_trans ?_ (rawCubicMultiplierEnergy_le_sqrtScale hlambda hK hrho
      hrhopi ha horder hfive)
    refine le_trans ?_ (sq_mul_integral_le_rawCubicMultiplierEnergy hlambda hK
      hrhopiLe ha (p₂ := p 1))
    exact mul_le_mul_of_nonneg_left
      (sq_norm_correctionType112Coefficients_le hlambda |p 0| (p 1)) (sq_nonneg _)
  have hweight : 2 * Manhattan.Estimates.dispersion (p 0) +
      2 * Manhattan.Estimates.dispersion (p 1 + p 1) ≤ 5 * |p 0| ^ 2 := by
    have h0 := Manhattan.Estimates.dispersion_le_half_mul_sq (p 0)
    have h1 := Manhattan.Estimates.dispersion_le_half_mul_sq (p 1 + p 1)
    have habs0 : (p 0) ^ 2 = |p 0| ^ 2 := (sq_abs (p 0)).symm
    have habs1 : (p 1) ^ 2 ≤ |p 0| ^ 2 := by
      rw [← sq_abs (p 1)]
      exact pow_le_pow_left₀ (abs_nonneg _) horder 2
    nlinarith [h0, h1, habs0, habs1]
  have hcnn : (0 : ℝ) ≤ ‖c‖ ^ 2 := sq_nonneg _
  rw [hk]
  nlinarith [hbridge, hshift, hcore, hmass, hweight, hcnn]

/-- **Summand 2 of (22) for the concrete competitor.** With the `(shift)`
phase in place the momentum bridge is an identity rather than a factor-two
comparison: the degree-three `H` energy of `k_p` at the true momentum `p` is
exactly energy at the frozen momentum `(0,-p₂)`, and Lemma 5.2 then
gives `2C√L`. Compare `hThreeForm_correctionWalsh_le`, which is the same
bound for the *unshifted* coefficient and pays a factor seven plus an
`O(|p₁|²)‖k‖²` error for the missing phase. -/
theorem hThreeForm_shiftedCorrectionWalsh_le
    {q : Manhattan.Estimates.Parameters}
    (hlambda : 0 < q.lambda) (hK : 1 ≤ q.K) (hrho : 0 ≤ q.rho)
    (hrhopi : 3 * q.rho < Real.pi) {C : ℝ} (p : Fin 2 → ℝ)
    (horder : |p 1| ≤ |p 0|)
    (hfive : Manhattan.Estimates.PropositionFiveTwoIntegralBound 40 C q |p 0|) :
    hThreeForm q.lambda p
        (Manhattan.shiftedCorrectionWalsh (kappa := 40) (by norm_num) hlambda
          |p 0| (p 0) (p 1)) ≤
      2 * C * Real.sqrt (q.scaleLog |p 0|) := by
  have ha : (0 : ℝ) ≤ |p 0| := abs_nonneg _
  set c := Manhattan.correctionType112Coefficients (kappa := 40) (by norm_num)
    hlambda |p 0| (p 1) with hc
  have hk : Manhattan.shiftedCorrectionWalsh (kappa := 40) (by norm_num) hlambda
      |p 0| (p 0) (p 1) =
      Manhattan.type112WalshSynthesis
        (Manhattan.type112ShiftTwist (p 0) (p 1) c) := rfl
  rw [hk, hThreeForm_type112ShiftTwist_frozen]
  have hshift : hThreeForm q.lambda ![0, -(p 1)]
      (Manhattan.type112WalshSynthesis c) ≤
      rawCubicHWeightEnergy q |p 0| (p 1) :=
    hThreeForm_frozen_correctionWalsh_le hlambda |p 0| (p 1)
  exact hshift.trans ((rawCubicHWeightEnergy_le_core hlambda |p 0| (p 1)).trans
    (rawCubicCoreEnergy_le_sqrtScale hlambda hK hrho hrhopi ha horder hfive))

/-! ### Summand 2, discharged -/

/-- In the high-logarithmic regime the support interval is nonempty. (The formalization
proves the same statement as `support_of_logThreshold` in
`Manhattan/Glue/FinalDischarge.lean`; it is repeated here so that this file
does not import that one.) -/
theorem mixedSupport_of_logThreshold {q : Manhattan.Estimates.Parameters}
    (hK : 1 < q.K) (hr0 : 0 < q.r0) (hlambda : 0 < q.lambda) {a : ℝ} (ha : 0 ≤ a)
    (hlog : q.logThreshold < q.scaleLog a) :
    q.K * q.delta a < q.r0 := by
  have hdelta : 0 < q.delta a := by
    have : 0 < Real.sqrt q.lambda := Real.sqrt_pos.mpr hlambda
    rw [Manhattan.Estimates.Parameters.delta]
    linarith
  have hlogK : 0 < Real.log q.K := Real.log_pos hK
  have hpos : 2 * Real.log q.K + 2 <
      Manhattan.Estimates.logPos (q.r0 / q.delta a) := by
    rw [Manhattan.Estimates.Parameters.logThreshold,
      Manhattan.Estimates.Parameters.scaleLog] at hlog
    linarith
  have hposPos : 0 < Manhattan.Estimates.logPos (q.r0 / q.delta a) := by linarith
  have hlogEq : Manhattan.Estimates.logPos (q.r0 / q.delta a) =
      Real.log (q.r0 / q.delta a) := by
    rw [Manhattan.Estimates.logPos, max_eq_right]
    by_contra hcon
    push_neg at hcon
    rw [Manhattan.Estimates.logPos, max_eq_left hcon.le] at hposPos
    exact lt_irrefl _ hposPos
  rw [hlogEq] at hpos
  have hratioPos : 0 < q.r0 / q.delta a := div_pos hr0 hdelta
  have hKlt : Real.log q.K < Real.log (q.r0 / q.delta a) := by linarith
  have hKpos : (0 : ℝ) < q.K := by linarith
  have hlt := (Real.log_lt_log_iff hKpos hratioPos).mp hKlt
  calc q.K * q.delta a < (q.r0 / q.delta a) * q.delta a :=
        mul_lt_mul_of_pos_right hlt hdelta
    _ = q.r0 := by field_simp

/-- Proposition 4.2 for the corrected competitor's parameters. -/
theorem exists_propositionFiveTwo_mixed :
    ∃ C : ℝ, 0 < C ∧
      ∀ {lambda : ℝ}, 0 < lambda → lambda ≤ 1 → ∀ a : ℝ, 0 ≤ a →
        let q : Manhattan.Estimates.Parameters :=
          ⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩
        q.logThreshold < q.scaleLog a →
        Manhattan.Estimates.PropositionFiveTwoIntegralBound 40 C q a := by
  obtain ⟨c, C, hc, hC, hall⟩ :=
    Manhattan.Estimates.propositionFiveTwoClaim_proved
      correctedCompetitorK correctedCompetitorRho
      (by simp [correctedCompetitorK])
      (by simp only [correctedCompetitorRho]; positivity)
      (by simp [correctedCompetitorRho])
  refine ⟨C, hC, ?_⟩
  intro lambda hlambda hlambdaOne a ha
  let q : Manhattan.Estimates.Parameters :=
    ⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩
  change q.logThreshold < q.scaleLog a → _
  intro hlog
  have hK : (1 : ℝ) < q.K := by simp [q, correctedCompetitorK]
  have hr0 : 0 < q.r0 := by
    simp only [q, Manhattan.Estimates.Parameters.r0, correctedCompetitorK,
      correctedCompetitorRho]
    positivity
  exact (hall lambda hlambda hlambdaOne a ha
    (mixedSupport_of_logThreshold hK hr0 hlambda ha hlog)).2.2

/-- **Summand 2 is discharged.** -/
theorem summandTwoBound_proved : ∃ C : ℝ, 0 ≤ C ∧ SummandTwoBound C := by
  obtain ⟨C, hC, hfive⟩ := exists_propositionFiveTwo_mixed
  refine ⟨2 * C, by linarith, ?_⟩
  intro lambda hlambda hlambdaOne p hp₀ hp₁ horder hpositive
  let q : Manhattan.Estimates.Parameters :=
    ⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩
  change q.logThreshold < q.scaleLog |p 0| → _
  intro hlog hcert hnormalization
  have hK : (1 : ℝ) ≤ q.K := by simp [q, correctedCompetitorK]
  have hrho : (0 : ℝ) ≤ q.rho := by
    simp only [q, correctedCompetitorRho]
    positivity
  have hrhopi : 3 * q.rho < Real.pi := by
    simp only [q, correctedCompetitorRho]
    nlinarith [Real.pi_pos]
  have hmain := hThreeForm_shiftedCorrectionWalsh_le (q := q) hlambda hK hrho
    hrhopi p horder (hfive hlambda hlambdaOne |p 0| (abs_nonneg _) hlog)
  refine le_trans ?_ hmain
  show (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hEnergy lambda
      (correctedMixedVector
        (correctedLowDegreeData hlambda p hcert hnormalization)) ≤ _
  rw [correctedMixedVector_eq,
    correctedLowDegreeData_mixed_eq hlambda p hcert hnormalization]
  exact hEnergy_ofReal_sign_smul_le _ hlambda.le _ _

end Manhattan.Glue
