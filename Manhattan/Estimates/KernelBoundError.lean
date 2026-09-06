import Manhattan.Estimates.KernelBound
import Manhattan.Estimates.DegreeThree

/-!
# Step 3 of Lemma 5.4: the error term at negative row frequencies

This file defines the error term `U(-s,β)` of `manuscript.tex:1349-1355`
(equation `(err)`), its squared `H⁻¹` norm, and proves the bound `(ebound)` of
`manuscript.tex:1394-1398`,
`‖U‖²_{-1,λ} ≤ C ∫∫ σ |v|²`, with an explicit constant.

The proof follows the paper: the support facts `(support)`, the lower bound
`(sigmalow)` for `σ`, the explicit kernel bound, and the Hilbert--Schmidt
estimate.  The last step uses `Manhattan.Estimates.torusIntegral_kernel_sq_le`
rather than a Hilbert--Schmidt operator theory, which Mathlib v4.26.0 does not
have.

Paper: `manuscript.tex:1356-1400`.
-/

open MeasureTheory Set

namespace Manhattan.Estimates

noncomputable section

/-- Classical decidability, local to this file: the statements here are analytic, not computational. -/
local instance kernelBoundErrorPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-! ### Elementary consequences of admissibility -/

theorem dispersion_le_two (s : ℝ) : dispersion s ≤ 2 := by
  have := Real.neg_one_le_cos s
  simp only [dispersion]
  linarith

/-- Every value of the multiplier `M` is at most `360` for `λ ≤ 1`. -/
theorem multiplier_le_360 {q : Parameters} (hlam : q.lambda ≤ 1) (P : Fin 2 → ℝ) :
    multiplier 40 q P ≤ 360 := by
  have h0 := dispersion_le_two (P 0)
  have h1 := dispersion_le_two (P 1)
  have hs0 : |Real.sin (P 0 / 2)| ≤ 1 := Real.abs_sin_le_one _
  have hs1 : |Real.sin (P 1 / 2)| ≤ 1 := Real.abs_sin_le_one _
  simp only [multiplier, theta]
  linarith

/-- The lower half of `(Mcomp)` for the ambient parameter record. -/
theorem multiplier_lower_of_separated {q : Parameters} (hq : q.Admissible)
    {beta alpha : ℝ} (halpha : |alpha| ≤ q.rho)
    (hsep : 4 * q.K * (Real.sqrt q.lambda + |beta|) ≤ |alpha|) :
    (80 / Real.pi) * |alpha| ≤ multiplier 40 q (mixedTotalFrequency beta alpha) :=
  (multiplier_comparison_explicit (K := q.K) (rho := q.rho) (lambda := q.lambda)
    (beta := beta) (alpha := alpha) hq.2.2.1 hq.2.2.2.2 hq.1 hq.2.1 halpha hsep).1

theorem delta_pos {q : Parameters} (hq : q.Admissible) {a : ℝ} (ha : 0 ≤ a) :
    0 < q.delta a :=
  add_pos_of_pos_of_nonneg (Real.sqrt_pos.2 hq.1) ha

theorem sqrt_lambda_le_delta (q : Parameters) {a : ℝ} (ha : 0 ≤ a) :
    Real.sqrt q.lambda ≤ q.delta a := by
  simp only [Parameters.delta]; linarith

theorem le_delta (q : Parameters) (a : ℝ) : a ≤ q.delta a := by
  simp only [Parameters.delta]
  linarith [Real.sqrt_nonneg q.lambda]

theorem K_pos {q : Parameters} (hq : q.Admissible) : 0 < q.K := by linarith [hq.2.2.1]

theorem rho_pos {q : Parameters} (hq : q.Admissible) : 0 < q.rho := hq.2.2.2.1

theorem sin_sq_le_sq (x : ℝ) : Real.sin x ^ 2 ≤ x ^ 2 := by
  have h := Real.abs_sin_le_abs (x := x)
  have h1 : Real.sin x ^ 2 = |Real.sin x| ^ 2 := (sq_abs _).symm
  have h2 : x ^ 2 = |x| ^ 2 := (sq_abs _).symm
  rw [h1, h2]
  exact pow_le_pow_left₀ (abs_nonneg _) h 2

/-! ### The support facts (support) -/

/-- Membership in `J(t,β)` forces the defining condition of `J` and the two
endpoint inequalities. -/
theorem mem_correctionInterval_iff' {q : Parameters} {a t beta alpha : ℝ}
    (hmem : alpha ∈ correctionInterval q a t beta) :
    (t ∈ q.supportInterval a ∧
        t + q.delta a + |beta| ≤ q.rho / (8 * q.K)) ∧
      -q.rho ≤ alpha ∧ alpha ≤ -(4 * q.K * (t + q.delta a + |beta|)) := by
  by_cases hcond : t ∈ q.supportInterval a ∧
      t + q.delta a + |beta| ≤ q.rho / (8 * q.K)
  · rw [correctionInterval, if_pos hcond] at hmem
    exact ⟨hcond, hmem.1, by linarith [hmem.2]⟩
  · rw [correctionInterval, if_neg hcond] at hmem
    exact absurd hmem (Set.notMem_empty alpha)

/-- Equation `(support)` of `manuscript.tex:1358-1366`: on the support of the
integrand in `(err)` the negative row frequency `s` dominates
`4K(t+δ+|β|)` and the multiplier is comparable to `s`. -/
theorem errorIntegrand_support {q : Parameters} (hq : q.Admissible)
    {a p₂ s t beta : ℝ} (ha : 0 ≤ a) (hp₂ : |p₂| ≤ a)
    (hmem : -s + t - p₂ ∈ correctionInterval q a t beta) :
    (t ∈ q.supportInterval a ∧
        t + q.delta a + |beta| ≤ q.rho / (8 * q.K)) ∧
      4 * q.K * (t + q.delta a + |beta|) ≤ s ∧
      (40 / Real.pi) * s ≤
        multiplier 40 q (mixedTotalFrequency beta (-s + t - p₂)) := by
  obtain ⟨hcond, hlow, hhigh⟩ := mem_correctionInterval_iff' hmem
  have hK : (20 : ℝ) ≤ q.K := hq.2.2.1
  have hKpos : 0 < q.K := by linarith
  have hdelta : 0 < q.delta a := delta_pos hq ha
  have hsqrtle : Real.sqrt q.lambda ≤ q.delta a := sqrt_lambda_le_delta q ha
  have hale : a ≤ q.delta a := le_delta q a
  have hp₂le : p₂ ≤ a := (abs_le.mp hp₂).2
  have hp₂ge : -a ≤ p₂ := (abs_le.mp hp₂).1
  have htK : q.K * q.delta a ≤ t := hcond.1.1
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) htK
  have htdelta : q.delta a ≤ t := by nlinarith
  have htp₂ : p₂ ≤ t := by linarith
  have hbeta : 0 ≤ |beta| := abs_nonneg beta
  have hsum : 0 ≤ t + q.delta a + |beta| := by linarith
  have hneg : -s + t - p₂ ≤ 0 := by nlinarith
  have habs : |(-s + t - p₂)| = s - t + p₂ := by
    rw [abs_of_nonpos hneg]; ring
  have hbig : 4 * q.K * (t + q.delta a + |beta|) ≤ s - t + p₂ := by linarith
  have hsupp : 4 * q.K * (t + q.delta a + |beta|) ≤ s := by linarith
  have hrho : |(-s + t - p₂)| ≤ q.rho := by rw [habs]; linarith
  have hsep : 4 * q.K * (Real.sqrt q.lambda + |beta|) ≤ |(-s + t - p₂)| := by
    rw [habs]
    have hmono : 4 * q.K * (Real.sqrt q.lambda + |beta|) ≤
        4 * q.K * (t + q.delta a + |beta|) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    linarith
  have hM := multiplier_lower_of_separated hq hrho hsep
  -- `s` is at most twice `|α|`
  have hcompare : t + q.delta a ≤ |(-s + t - p₂)| := by
    have h80 : (80 : ℝ) * (t + q.delta a + |beta|) ≤
        4 * q.K * (t + q.delta a + |beta|) := by nlinarith
    have h1 : t + q.delta a ≤ t + q.delta a + |beta| := by linarith
    rw [habs]
    nlinarith
  have hhalf : s ≤ 2 * |(-s + t - p₂)| := by
    rw [habs] at hcompare ⊢
    linarith
  refine ⟨hcond, hsupp, ?_⟩
  have hpi : 0 < Real.pi := Real.pi_pos
  calc (40 / Real.pi) * s ≤ (40 / Real.pi) * (2 * |(-s + t - p₂)|) := by
        apply mul_le_mul_of_nonneg_left hhalf (by positivity)
    _ = (80 / Real.pi) * |(-s + t - p₂)| := by ring
    _ ≤ _ := hM

/-! ### The lower bound (sigmalow) -/

/-- Equation `(sigmalow)` of `manuscript.tex:1370-1374`: when `J(t,β)` is
non-empty it contains `[-ρ,-ρ/2]`, and hence `σ(t,β) ≥ c sin²β`. -/
theorem correctionSigma_lower {q : Parameters} (hq : q.Admissible) {a t beta : ℝ}
    (hcond : t ∈ q.supportInterval a ∧
      t + q.delta a + |beta| ≤ q.rho / (8 * q.K)) :
    q.rho / (1440 * Real.pi) * Real.sin beta ^ 2 ≤
      correctionSigma 40 q a t beta := by
  have hK : (20 : ℝ) ≤ q.K := hq.2.2.1
  have hKpos : 0 < q.K := by linarith
  have hrho : 0 < q.rho := hq.2.2.2.1
  have hrhopi : q.rho ≤ Real.pi / 20 := hq.2.2.2.2
  have hpi : 0 < Real.pi := Real.pi_pos
  have hlam : 0 < q.lambda := hq.1
  have hlam1 : q.lambda ≤ 1 := hq.2.1
  -- the interval is the explicit `Icc`
  have hJ : correctionInterval q a t beta =
      Set.Icc (-q.rho) (-4 * q.K * (t + q.delta a + |beta|)) := by
    rw [correctionInterval, if_pos hcond]
  have hhalf : 4 * q.K * (t + q.delta a + |beta|) ≤ q.rho / 2 := by
    have := hcond.2
    have h8 : (0 : ℝ) < 8 * q.K := by linarith
    rw [le_div_iff₀ h8] at this
    nlinarith
  have hsub : Set.Icc (-q.rho) (-(q.rho / 2)) ⊆ correctionInterval q a t beta := by
    rw [hJ]
    intro x hx
    exact ⟨hx.1, by linarith [hx.2]⟩
  have hsubtorus : Set.Icc (-q.rho) (-(q.rho / 2)) ⊆ torus := by
    intro x hx
    constructor
    · have : -Real.pi < -q.rho := by linarith
      linarith [hx.1]
    · linarith [hx.2]
  -- the integrand of `σ`
  set f : ℝ → ℝ := fun alpha =>
    if alpha ∈ correctionInterval q a t beta then
      (multiplier 40 q (mixedTotalFrequency beta alpha))⁻¹
    else 0 with hfdef
  have hMpos : ∀ alpha : ℝ, 0 < multiplier 40 q (mixedTotalFrequency beta alpha) :=
    fun alpha => multiplier_pos (by norm_num) hlam _
  have hfnn : ∀ alpha, 0 ≤ f alpha := by
    intro alpha
    rw [hfdef]
    dsimp only
    split_ifs
    · exact (inv_pos.2 (hMpos alpha)).le
    · exact le_rfl
  have hfmeas : Measurable f := by
    rw [hfdef]
    refine Measurable.ite ?_ ?_ measurable_const
    · rw [hJ]; exact measurableSet_Icc
    · simp only [multiplier, mixedTotalFrequency, theta, Matrix.cons_val_zero,
        Matrix.cons_val_one, dispersion]
      fun_prop
  have hfbound : ∀ alpha, |f alpha| ≤ (40 * q.lambda)⁻¹ := by
    intro alpha
    rw [abs_of_nonneg (hfnn alpha), hfdef]
    dsimp only
    split_ifs
    · refine inv_anti₀ (by positivity) ?_
      simp only [multiplier]
      have := theta_nonneg (mixedTotalFrequency beta alpha)
      have h0 : 0 ≤ |Real.sin (mixedTotalFrequency beta alpha 0 / 2)| := abs_nonneg _
      have h1 : 0 ≤ |Real.sin (mixedTotalFrequency beta alpha 1 / 2)| := abs_nonneg _
      nlinarith
    · positivity
  have hfint : Integrable f (volume.restrict torus) :=
    integrableOn_torus_of_bounded hfmeas hfbound
  -- pointwise comparison with the constant on `[-ρ,-ρ/2]`
  have hpt : ∀ alpha : ℝ,
      (if alpha ∈ Set.Icc (-q.rho) (-(q.rho / 2)) then (360 : ℝ)⁻¹ else 0) ≤
        f alpha := by
    intro alpha
    by_cases hx : alpha ∈ Set.Icc (-q.rho) (-(q.rho / 2))
    · rw [if_pos hx, hfdef]
      dsimp only
      rw [if_pos (hsub hx)]
      exact inv_anti₀ (hMpos alpha) (multiplier_le_360 hlam1 _)
    · rw [if_neg hx]
      exact hfnn alpha
  have hmono := torusIntegral_mono' (f := fun alpha =>
      if alpha ∈ Set.Icc (-q.rho) (-(q.rho / 2)) then (360 : ℝ)⁻¹ else 0)
    (g := f)
    (fun x => by by_cases h : x ∈ Set.Icc (-q.rho) (-(q.rho / 2)) <;> simp [h]) hfint hpt
  have hval := torusIntegral_indicator_const_Icc (u := -q.rho) (v := -(q.rho / 2))
    (c := (360 : ℝ)⁻¹) (by linarith) hsubtorus
  rw [hval] at hmono
  have heq : (2 * Real.pi)⁻¹ * ((360 : ℝ)⁻¹ * (-(q.rho / 2) - -q.rho)) =
      q.rho / (1440 * Real.pi) := by
    field_simp
    ring
  rw [heq] at hmono
  have hkey : q.rho / (1440 * Real.pi) ≤ torusIntegral f := hmono
  have hsin : 0 ≤ Real.sin beta ^ 2 := sq_nonneg _
  have hfinal : q.rho / (1440 * Real.pi) * Real.sin beta ^ 2 ≤
      Real.sin beta ^ 2 * torusIntegral f := by
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left hkey hsin
  rw [correctionSigma]
  exact hfinal

/-! ### Basic bounds on `σ` and `v` -/

theorem correctionSigma_le_inv {q : Parameters} (hq : q.Admissible) (a r beta : ℝ) :
    correctionSigma 40 q a r beta ≤ (40 * q.lambda)⁻¹ := by
  have hlam : 0 < q.lambda := hq.1
  have hMpos : ∀ alpha : ℝ, 0 < multiplier 40 q (mixedTotalFrequency beta alpha) :=
    fun alpha => multiplier_pos (by norm_num) hlam _
  set f : ℝ → ℝ := fun alpha =>
    if alpha ∈ correctionInterval q a r beta then
      (multiplier 40 q (mixedTotalFrequency beta alpha))⁻¹
    else 0 with hfdef
  have hfnn : ∀ alpha, 0 ≤ f alpha := by
    intro alpha
    rw [hfdef]; dsimp only
    split_ifs
    · exact (inv_pos.2 (hMpos alpha)).le
    · exact le_rfl
  have hfle : ∀ alpha, f alpha ≤ (40 * q.lambda)⁻¹ := by
    intro alpha
    rw [hfdef]; dsimp only
    split_ifs
    · refine inv_anti₀ (by positivity) ?_
      simp only [multiplier]
      have h := theta_nonneg (mixedTotalFrequency beta alpha)
      have h0 : 0 ≤ |Real.sin (mixedTotalFrequency beta alpha 0 / 2)| := abs_nonneg _
      have h1 : 0 ≤ |Real.sin (mixedTotalFrequency beta alpha 1 / 2)| := abs_nonneg _
      nlinarith
    · positivity
  have hint : torusIntegral f ≤ (40 * q.lambda)⁻¹ := by
    have := torusIntegral_mono' (f := f) (g := fun _ : ℝ => (40 * q.lambda)⁻¹) hfnn
      (integrable_const _) hfle
    simpa [torusIntegral_const'] using this
  have hsin : Real.sin beta ^ 2 ≤ 1 := by
    have := Real.sin_sq_add_cos_sq beta
    nlinarith [sq_nonneg (Real.cos beta)]
  have hnn : 0 ≤ torusIntegral f := torusIntegral_nonneg' hfnn
  have : Real.sin beta ^ 2 * torusIntegral f ≤ (40 * q.lambda)⁻¹ := by
    nlinarith [sq_nonneg (Real.sin beta)]
  rw [correctionSigma]
  exact this

theorem correctionV_nonneg {q : Parameters} (hq : q.Admissible) (a r beta : ℝ) :
    0 ≤ correctionV 40 q a r beta := by
  rw [correctionV]
  split_ifs
  · exact (inv_pos.2 (correctionDenominator_pos (by norm_num) hq.1 a r beta)).le
  · exact le_rfl

theorem correctionV_le_inv {q : Parameters} (hq : q.Admissible) (a r beta : ℝ) :
    correctionV 40 q a r beta ≤ q.lambda⁻¹ := by
  have hlam : 0 < q.lambda := hq.1
  rw [correctionV]
  split_ifs
  · refine inv_anti₀ hlam ?_
    have hB : q.lambda ≤ correctionB q r beta := by
      simp only [correctionB]
      linarith [dispersion_nonneg r, dispersion_nonneg beta]
    linarith [correctionSigma_nonneg (by norm_num : (0:ℝ) < 40) hlam a r beta]
  · positivity

/-! ### Measurability -/

theorem correctionSigma_measurable_left (kappa : ℝ) (q : Parameters) (a beta : ℝ) :
    Measurable (fun r : ℝ => correctionSigma kappa q a r beta) := by
  change Measurable ((fun z : ℝ × ℝ => correctionSigma kappa q a z.1 z.2) ∘
    fun r : ℝ => (r, beta))
  exact (correctionSigma_measurable kappa q a).comp measurable_prodMk_right

theorem correctionV_measurable (kappa : ℝ) (q : Parameters) (a : ℝ) :
    Measurable (fun z : ℝ × ℝ => correctionV kappa q a z.1 z.2) := by
  have hset : MeasurableSet {z : ℝ × ℝ | z.1 ∈ q.supportInterval a} := by
    have : {z : ℝ × ℝ | z.1 ∈ q.supportInterval a} =
        (q.supportInterval a) ×ˢ (Set.univ : Set ℝ) := by
      ext z; simp
    rw [this, Parameters.supportInterval]
    exact measurableSet_Icc.prod MeasurableSet.univ
  refine Measurable.ite hset ?_ measurable_const
  refine Measurable.inv ?_
  refine Measurable.add ?_ (correctionSigma_measurable kappa q a)
  simp only [correctionB, dispersion]
  fun_prop

theorem correctionV_measurable_left (kappa : ℝ) (q : Parameters) (a beta : ℝ) :
    Measurable (fun r : ℝ => correctionV kappa q a r beta) := by
  change Measurable ((fun z : ℝ × ℝ => correctionV kappa q a z.1 z.2) ∘
    fun r : ℝ => (r, beta))
  exact (correctionV_measurable kappa q a).comp measurable_prodMk_right

theorem measurableSet_errorSupport (q : Parameters) (a p₂ s beta : ℝ) :
    MeasurableSet {t : ℝ | -s + t - p₂ ∈ correctionInterval q a t beta} := by
  unfold correctionInterval Parameters.supportInterval Parameters.delta Parameters.r0
  simp only [Set.mem_ite_empty_right, Set.mem_Icc]
  measurability

/-! ### The error term and its `H⁻¹` norm -/

/-- The error term `U(-s,β)` at negative row frequencies,
`manuscript.tex:1349-1355` (equation `(err)`).  The paper's `∫_I` is
automatic: `v` and `J` both vanish off the support interval `I`. -/
noncomputable def errorU (q : Parameters) (a p₂ s beta : ℝ) : ℝ :=
  Real.sin beta ^ 2 * torusIntegral (fun t : ℝ =>
    if -s + t - p₂ ∈ correctionInterval q a t beta then
      correctionV 40 q a t beta *
        (multiplier 40 q (mixedTotalFrequency beta (-s + t - p₂)))⁻¹
    else 0)

/-- The squared `H⁻¹` norm of the error term.  `U` is supported at negative
row frequencies `r = -s`, `s > 0`, and the `H⁻¹` multiplier there is
`(λ+d(r)+d(β))⁻¹`. -/
noncomputable def errorHMinusSq (q : Parameters) (a p₂ : ℝ) : ℝ :=
  torusIntegral (fun beta : ℝ =>
    torusIntegral (fun s : ℝ =>
      if 0 < s then
        mixedHMinusWeight q (-s) beta * errorU q a p₂ s beta ^ 2
      else 0))

/-- The right-hand side of `(ebound)`: `∫∫ σ |v|² dm dm`. -/
noncomputable def correctionSigmaEnergyBeta (q : Parameters) (a : ℝ) : ℝ :=
  torusIntegral (fun beta : ℝ => torusIntegral (fun t : ℝ =>
    correctionSigma 40 q a t beta * correctionV 40 q a t beta ^ 2))

/-- The Cauchy--Schwarz factor `φ(t)=√σ(t,β) v(t,β)` of
`manuscript.tex:1376-1378`. -/
noncomputable def errorPhi (q : Parameters) (a t beta : ℝ) : ℝ :=
  Real.sqrt (correctionSigma 40 q a t beta) * correctionV 40 q a t beta

/-- The majorant kernel `C sin²β / (s² √σ(t,β)) 1_{s ≥ 4K(t+δ+|β|)}` of
`manuscript.tex:1379-1384`, with `C = 1`. -/
noncomputable def errorKernel (q : Parameters) (a p₂ s beta t : ℝ) : ℝ :=
  if -s + t - p₂ ∈ correctionInterval q a t beta then
    Real.sin beta ^ 2 / (s ^ 2 * Real.sqrt (correctionSigma 40 q a t beta))
  else 0

/-- The constant `c` of `(sigmalow)`. -/
noncomputable def sigmaLowerConstant (q : Parameters) : ℝ :=
  q.rho / (1440 * Real.pi)

/-- The explicit constant in `(ebound)`. -/
noncomputable def errorKernelConstant (q : Parameters) : ℝ :=
  3 / (q.K ^ 3 * q.rho)

theorem sigmaLowerConstant_pos {q : Parameters} (hq : q.Admissible) :
    0 < sigmaLowerConstant q := by
  have := hq.2.2.2.1
  have := Real.pi_pos
  unfold sigmaLowerConstant
  positivity

theorem errorPhi_nonneg {q : Parameters} (hq : q.Admissible) (a t beta : ℝ) :
    0 ≤ errorPhi q a t beta :=
  mul_nonneg (Real.sqrt_nonneg _) (correctionV_nonneg hq a t beta)

theorem errorPhi_sq {q : Parameters} (hq : q.Admissible) (a t beta : ℝ) :
    errorPhi q a t beta ^ 2 =
      correctionSigma 40 q a t beta * correctionV 40 q a t beta ^ 2 := by
  unfold errorPhi
  rw [mul_pow, Real.sq_sqrt
    (correctionSigma_nonneg (by norm_num) hq.1 a t beta)]

theorem errorPhi_le {q : Parameters} (hq : q.Admissible) (a t beta : ℝ) :
    errorPhi q a t beta ≤
      Real.sqrt ((40 * q.lambda)⁻¹) * q.lambda⁻¹ := by
  have h1 : Real.sqrt (correctionSigma 40 q a t beta) ≤
      Real.sqrt ((40 * q.lambda)⁻¹) :=
    Real.sqrt_le_sqrt (correctionSigma_le_inv hq a t beta)
  have h2 : correctionV 40 q a t beta ≤ q.lambda⁻¹ := correctionV_le_inv hq a t beta
  exact mul_le_mul h1 h2 (correctionV_nonneg hq a t beta) (Real.sqrt_nonneg _)

theorem errorPhi_measurable (q : Parameters) (a beta : ℝ) :
    Measurable (fun t : ℝ => errorPhi q a t beta) := by
  unfold errorPhi
  exact (Real.continuous_sqrt.measurable.comp
    (correctionSigma_measurable_left 40 q a beta)).mul
    (correctionV_measurable_left 40 q a beta)

theorem errorPhi_sq_integrable {q : Parameters} (hq : q.Admissible) (a beta : ℝ) :
    Integrable (fun t : ℝ => errorPhi q a t beta ^ 2) (volume.restrict torus) := by
  refine integrableOn_torus_of_bounded ((errorPhi_measurable q a beta).pow_const 2)
    (C := (Real.sqrt ((40 * q.lambda)⁻¹) * q.lambda⁻¹) ^ 2) ?_
  intro t
  rw [abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (errorPhi_nonneg hq a t beta) (errorPhi_le hq a t beta) 2

theorem errorKernel_nonneg (q : Parameters)
    (a p₂ s beta t : ℝ) : 0 ≤ errorKernel q a p₂ s beta t := by
  unfold errorKernel
  split_ifs
  · positivity
  · exact le_rfl

theorem errorKernel_measurable (q : Parameters) (a p₂ s beta : ℝ) :
    Measurable (fun t : ℝ => errorKernel q a p₂ s beta t) := by
  unfold errorKernel
  refine Measurable.ite (measurableSet_errorSupport q a p₂ s beta) ?_ measurable_const
  exact measurable_const.div (measurable_const.mul
    (Real.continuous_sqrt.measurable.comp
      (correctionSigma_measurable_left 40 q a beta)))

/-- On the support of the kernel, `√σ ≥ √c |sin β|`, which is the only place
`(sigmalow)` is used. -/
theorem sqrt_correctionSigma_lower {q : Parameters} (hq : q.Admissible)
    {a t beta : ℝ}
    (hcond : t ∈ q.supportInterval a ∧
      t + q.delta a + |beta| ≤ q.rho / (8 * q.K)) :
    Real.sqrt (sigmaLowerConstant q) * |Real.sin beta| ≤
      Real.sqrt (correctionSigma 40 q a t beta) := by
  have hc : 0 < sigmaLowerConstant q := sigmaLowerConstant_pos hq
  have hlow : sigmaLowerConstant q * Real.sin beta ^ 2 ≤
      correctionSigma 40 q a t beta := correctionSigma_lower hq hcond
  have hsplit : Real.sqrt (sigmaLowerConstant q * Real.sin beta ^ 2) =
      Real.sqrt (sigmaLowerConstant q) * |Real.sin beta| := by
    rw [Real.sqrt_mul hc.le, Real.sqrt_sq_eq_abs]
  rw [← hsplit]
  exact Real.sqrt_le_sqrt hlow

/-- A uniform bound on the majorant kernel, used only for integrability. -/
theorem errorKernel_le {q : Parameters} (hq : q.Admissible) {a p₂ s beta : ℝ}
    (ha : 0 ≤ a) (hp₂ : |p₂| ≤ a) (hs : 0 < s) (t : ℝ) :
    errorKernel q a p₂ s beta t ≤
      (s ^ 2 * Real.sqrt (sigmaLowerConstant q))⁻¹ := by
  have hc : 0 < sigmaLowerConstant q := sigmaLowerConstant_pos hq
  have hcs : 0 < Real.sqrt (sigmaLowerConstant q) := Real.sqrt_pos.2 hc
  have hs2 : 0 < s ^ 2 := by positivity
  unfold errorKernel
  split_ifs with hmem
  · obtain ⟨hcond, -, -⟩ := errorIntegrand_support hq ha hp₂ hmem
    have hsq := sqrt_correctionSigma_lower hq hcond
    by_cases hsin : Real.sin beta = 0
    · simp [hsin]
      positivity
    · have habs : 0 < |Real.sin beta| := abs_pos.2 hsin
      have hpos : 0 < Real.sqrt (correctionSigma 40 q a t beta) := by
        have : 0 < Real.sqrt (sigmaLowerConstant q) * |Real.sin beta| := by positivity
        linarith
      rw [div_le_iff₀ (by positivity)]
      rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]
      have hsinsq : Real.sin beta ^ 2 = |Real.sin beta| ^ 2 := (sq_abs _).symm
      calc Real.sin beta ^ 2 * (s ^ 2 * Real.sqrt (sigmaLowerConstant q))
          = |Real.sin beta| * (s ^ 2 *
              (Real.sqrt (sigmaLowerConstant q) * |Real.sin beta|)) := by
            rw [hsinsq]; ring
        _ ≤ 1 * (s ^ 2 * Real.sqrt (correctionSigma 40 q a t beta)) := by
            apply mul_le_mul _ _ (by positivity) (by norm_num)
            · exact Real.abs_sin_le_one beta
            · exact mul_le_mul_of_nonneg_left hsq hs2.le
        _ = s ^ 2 * Real.sqrt (correctionSigma 40 q a t beta) := by ring
  · positivity

theorem errorKernel_sq_integrable {q : Parameters} (hq : q.Admissible)
    {a p₂ s beta : ℝ} (ha : 0 ≤ a) (hp₂ : |p₂| ≤ a) (hs : 0 < s) :
    Integrable (fun t : ℝ => errorKernel q a p₂ s beta t ^ 2)
      (volume.restrict torus) := by
  refine integrableOn_torus_of_bounded
    ((errorKernel_measurable q a p₂ s beta).pow_const 2)
    (C := ((s ^ 2 * Real.sqrt (sigmaLowerConstant q))⁻¹) ^ 2) ?_
  intro t
  rw [abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (errorKernel_nonneg q a p₂ s beta t)
    (errorKernel_le hq ha hp₂ hs t) 2

theorem errorKernel_mul_errorPhi_integrable {q : Parameters} (hq : q.Admissible)
    {a p₂ s beta : ℝ} (ha : 0 ≤ a) (hp₂ : |p₂| ≤ a) (hs : 0 < s) :
    Integrable (fun t : ℝ => errorKernel q a p₂ s beta t * errorPhi q a t beta)
      (volume.restrict torus) := by
  refine integrableOn_torus_of_bounded
    ((errorKernel_measurable q a p₂ s beta).mul (errorPhi_measurable q a beta))
    (C := (s ^ 2 * Real.sqrt (sigmaLowerConstant q))⁻¹ *
      (Real.sqrt ((40 * q.lambda)⁻¹) * q.lambda⁻¹)) ?_
  intro t
  rw [abs_of_nonneg (mul_nonneg (errorKernel_nonneg q a p₂ s beta t)
    (errorPhi_nonneg hq a t beta))]
  exact mul_le_mul (errorKernel_le hq ha hp₂ hs t) (errorPhi_le hq a t beta)
    (errorPhi_nonneg hq a t beta)
    (le_trans (errorKernel_nonneg q a p₂ s beta t) (errorKernel_le hq ha hp₂ hs t))

/-! ### The kernel bound of Step 3 -/

theorem mixedHMinusWeight_le {q : Parameters} (hq : q.Admissible) {s beta : ℝ}
    (hs : 0 < s) (hspi : s ≤ Real.pi) :
    mixedHMinusWeight q (-s) beta ≤ Real.pi ^ 2 / (2 * s ^ 2) := by
  have hsabs : |(-s)| ≤ Real.pi := by
    rw [abs_neg, abs_of_pos hs]; exact hspi
  have hlow := (dispersion_quadratic_bounds hsabs).1
  have hpi : 0 < Real.pi := Real.pi_pos
  have hden : 2 * s ^ 2 / Real.pi ^ 2 ≤
      q.lambda + dispersion (-s) + dispersion beta := by
    have := dispersion_nonneg beta
    have hl := hq.1
    calc 2 * s ^ 2 / Real.pi ^ 2 = 2 * (-s) ^ 2 / Real.pi ^ 2 := by ring_nf
      _ ≤ dispersion (-s) := hlow
      _ ≤ _ := by linarith
  have hpos : (0 : ℝ) < 2 * s ^ 2 / Real.pi ^ 2 := by positivity
  have := inv_anti₀ hpos hden
  calc mixedHMinusWeight q (-s) beta = (q.lambda + dispersion (-s) +
      dispersion beta)⁻¹ := rfl
    _ ≤ (2 * s ^ 2 / Real.pi ^ 2)⁻¹ := this
    _ = Real.pi ^ 2 / (2 * s ^ 2) := by
        rw [inv_div]

/-- The pointwise kernel estimate of `manuscript.tex:1376-1384`. -/
theorem errorU_integrand_le {q : Parameters} (hq : q.Admissible)
    {a p₂ s beta : ℝ} (ha : 0 ≤ a) (hp₂ : |p₂| ≤ a) (hs : 0 < s)
    (hspi : s ≤ Real.pi) (t : ℝ) :
    (Real.sqrt (mixedHMinusWeight q (-s) beta) * Real.sin beta ^ 2) *
        (if -s + t - p₂ ∈ correctionInterval q a t beta then
          correctionV 40 q a t beta *
            (multiplier 40 q (mixedTotalFrequency beta (-s + t - p₂)))⁻¹
        else 0)
      ≤ errorKernel q a p₂ s beta t * errorPhi q a t beta := by
  have hs2 : (0 : ℝ) < s ^ 2 := by positivity
  have hpi : 0 < Real.pi := Real.pi_pos
  by_cases hmem : -s + t - p₂ ∈ correctionInterval q a t beta
  · obtain ⟨hcond, -, hM⟩ := errorIntegrand_support hq ha hp₂ hmem
    by_cases hsin : Real.sin beta = 0
    · simp [hsin, errorKernel, errorPhi]
    · have hsqlow := sqrt_correctionSigma_lower hq hcond
      have habs : 0 < |Real.sin beta| := abs_pos.2 hsin
      have hcpos : 0 < Real.sqrt (sigmaLowerConstant q) :=
        Real.sqrt_pos.2 (sigmaLowerConstant_pos hq)
      have hsqpos : 0 < Real.sqrt (correctionSigma 40 q a t beta) := by
        have : 0 < Real.sqrt (sigmaLowerConstant q) * |Real.sin beta| := by positivity
        linarith
      have hMpos : 0 < multiplier 40 q (mixedTotalFrequency beta (-s + t - p₂)) :=
        multiplier_pos (by norm_num) hq.1 _
      have hmwnn : 0 ≤ mixedHMinusWeight q (-s) beta := by
        unfold mixedHMinusWeight
        have := mixed_denominator_pos hq.1 (-s) beta
        positivity
      have hR : 0 ≤ Real.sqrt (mixedHMinusWeight q (-s) beta) := Real.sqrt_nonneg _
      have hRsq : Real.sqrt (mixedHMinusWeight q (-s) beta) ^ 2 =
          mixedHMinusWeight q (-s) beta := Real.sq_sqrt hmwnn
      have hmwle := mixedHMinusWeight_le hq (beta := beta) hs hspi
      -- `R s² ≤ M`
      have hkeysq : (Real.sqrt (mixedHMinusWeight q (-s) beta) * s ^ 2) ^ 2 ≤
          (multiplier 40 q (mixedTotalFrequency beta (-s + t - p₂))) ^ 2 := by
        have h1 : (Real.sqrt (mixedHMinusWeight q (-s) beta) * s ^ 2) ^ 2 =
            mixedHMinusWeight q (-s) beta * s ^ 4 := by
          rw [mul_pow, hRsq]; ring
        have h2 : mixedHMinusWeight q (-s) beta * s ^ 4 ≤
            Real.pi ^ 2 / (2 * s ^ 2) * s ^ 4 := by
          apply mul_le_mul_of_nonneg_right hmwle (by positivity)
        have h3 : Real.pi ^ 2 / (2 * s ^ 2) * s ^ 4 = Real.pi ^ 2 * s ^ 2 / 2 := by
          field_simp
        have h4 : (40 / Real.pi) * s ≤
            multiplier 40 q (mixedTotalFrequency beta (-s + t - p₂)) := hM
        have h5 : ((40 / Real.pi) * s) ^ 2 ≤
            (multiplier 40 q (mixedTotalFrequency beta (-s + t - p₂))) ^ 2 := by
          apply pow_le_pow_left₀ (by positivity) h4
        have h6 : Real.pi ^ 2 * s ^ 2 / 2 ≤ ((40 / Real.pi) * s) ^ 2 := by
          rw [mul_pow, div_pow]
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by norm_num) (by positivity)]
          have hpi4 : Real.pi ≤ 4 := Real.pi_le_four
          have hpi2 : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_pos]
          have hpi4th : Real.pi ^ 2 * Real.pi ^ 2 ≤ 256 := by
            nlinarith [sq_nonneg Real.pi]
          nlinarith [mul_nonneg (sub_nonneg.2 hpi4th) hs2.le]
        linarith
      have hkey : Real.sqrt (mixedHMinusWeight q (-s) beta) * s ^ 2 ≤
          multiplier 40 q (mixedTotalFrequency beta (-s + t - p₂)) := by
        have hnn : 0 ≤ Real.sqrt (mixedHMinusWeight q (-s) beta) * s ^ 2 := by positivity
        have := Real.sqrt_le_sqrt hkeysq
        rwa [Real.sqrt_sq hnn, Real.sqrt_sq hMpos.le] at this
      have hfrac : Real.sqrt (mixedHMinusWeight q (-s) beta) *
          (multiplier 40 q (mixedTotalFrequency beta (-s + t - p₂)))⁻¹ ≤
          (s ^ 2)⁻¹ := by
        rw [← div_eq_mul_inv, ← one_div, div_le_div_iff₀ hMpos hs2]
        linarith
      have hvnn : 0 ≤ correctionV 40 q a t beta := correctionV_nonneg hq a t beta
      have hnn : 0 ≤ Real.sin beta ^ 2 * correctionV 40 q a t beta := by positivity
      have hRHS : errorKernel q a p₂ s beta t * errorPhi q a t beta =
          Real.sin beta ^ 2 * correctionV 40 q a t beta / s ^ 2 := by
        unfold errorKernel errorPhi
        rw [if_pos hmem]
        field_simp
      rw [hRHS, if_pos hmem]
      calc (Real.sqrt (mixedHMinusWeight q (-s) beta) * Real.sin beta ^ 2) *
            (correctionV 40 q a t beta *
              (multiplier 40 q (mixedTotalFrequency beta (-s + t - p₂)))⁻¹)
          = (Real.sin beta ^ 2 * correctionV 40 q a t beta) *
              (Real.sqrt (mixedHMinusWeight q (-s) beta) *
                (multiplier 40 q (mixedTotalFrequency beta (-s + t - p₂)))⁻¹) := by
              ring
        _ ≤ (Real.sin beta ^ 2 * correctionV 40 q a t beta) * (s ^ 2)⁻¹ :=
              mul_le_mul_of_nonneg_left hfrac hnn
        _ = Real.sin beta ^ 2 * correctionV 40 q a t beta / s ^ 2 := by ring
  · rw [if_neg hmem, mul_zero]
    unfold errorKernel
    rw [if_neg hmem, zero_mul]

theorem sqrt_weight_mul_errorU_le {q : Parameters} (hq : q.Admissible)
    {a p₂ s beta : ℝ} (ha : 0 ≤ a) (hp₂ : |p₂| ≤ a) (hs : 0 < s)
    (hspi : s ≤ Real.pi) :
    Real.sqrt (mixedHMinusWeight q (-s) beta) * errorU q a p₂ s beta ≤
      torusIntegral (fun t : ℝ =>
        errorKernel q a p₂ s beta t * errorPhi q a t beta) := by
  have hR : 0 ≤ Real.sqrt (mixedHMinusWeight q (-s) beta) := Real.sqrt_nonneg _
  have hrewrite : Real.sqrt (mixedHMinusWeight q (-s) beta) * errorU q a p₂ s beta =
      torusIntegral (fun t : ℝ =>
        (Real.sqrt (mixedHMinusWeight q (-s) beta) * Real.sin beta ^ 2) *
          (if -s + t - p₂ ∈ correctionInterval q a t beta then
            correctionV 40 q a t beta *
              (multiplier 40 q (mixedTotalFrequency beta (-s + t - p₂)))⁻¹
          else 0)) := by
    rw [torusIntegral_smul_left, errorU, mul_assoc]
  rw [hrewrite]
  refine torusIntegral_mono' ?_
    (errorKernel_mul_errorPhi_integrable hq ha hp₂ hs)
    (errorU_integrand_le hq ha hp₂ hs hspi)
  intro t
  refine mul_nonneg (by positivity) ?_
  split_ifs
  · exact mul_nonneg (correctionV_nonneg hq a t beta)
      (inv_nonneg.2 (multiplier_pos (by norm_num) hq.1 _).le)
  · exact le_rfl

/-! ### The Hilbert--Schmidt estimate -/

/-- The `s`-majorant of the kernel energy, `manuscript.tex:1386-1393`. -/
noncomputable def errorSMajorant (q : Parameters) (beta s : ℝ) : ℝ :=
  if 4 * q.K * |beta| ≤ s then
    (2 * Real.pi)⁻¹ * (Real.sin beta ^ 2 / (sigmaLowerConstant q * (4 * q.K))) *
      (s ^ 3)⁻¹
  else 0

theorem errorSMajorant_nonneg {q : Parameters} (hq : q.Admissible) (beta s : ℝ) :
    0 ≤ errorSMajorant q beta s := by
  have hK : 0 < q.K := K_pos hq
  have hc : 0 < sigmaLowerConstant q := sigmaLowerConstant_pos hq
  unfold errorSMajorant
  split_ifs with h
  · have hs : 0 ≤ s := le_trans (by positivity) h
    have : (0 : ℝ) ≤ (s ^ 3)⁻¹ := by positivity
    positivity
  · exact le_rfl

/-- The kernel energy at a fixed negative row frequency. -/
theorem errorKernel_sq_integral_le {q : Parameters} (hq : q.Admissible)
    {a p₂ s beta : ℝ} (ha : 0 ≤ a) (hp₂ : |p₂| ≤ a) (hs : 0 < s) :
    torusIntegral (fun t : ℝ => errorKernel q a p₂ s beta t ^ 2) ≤
      errorSMajorant q beta s := by
  have hK : 0 < q.K := K_pos hq
  have hc : 0 < sigmaLowerConstant q := sigmaLowerConstant_pos hq
  have hs4 : (0 : ℝ) < s ^ 4 := by positivity
  by_cases hA : 4 * q.K * |beta| ≤ s
  · have hset : MeasurableSet {t : ℝ | -s + t - p₂ ∈ correctionInterval q a t beta} :=
      measurableSet_errorSupport q a p₂ s beta
    set M₀ : ℝ := Real.sin beta ^ 2 / (sigmaLowerConstant q * s ^ 4) with hM₀
    have hM₀nn : 0 ≤ M₀ := by rw [hM₀]; positivity
    have hpt : ∀ t : ℝ, errorKernel q a p₂ s beta t ^ 2 ≤
        (if t ∈ {t : ℝ | -s + t - p₂ ∈ correctionInterval q a t beta} then M₀
          else 0) := by
      intro t
      by_cases hmem : -s + t - p₂ ∈ correctionInterval q a t beta
      · have hmem' : t ∈ {t : ℝ | -s + t - p₂ ∈ correctionInterval q a t beta} := hmem
        rw [if_pos hmem']
        obtain ⟨hcond, -, -⟩ := errorIntegrand_support hq ha hp₂ hmem
        have hσnn : 0 ≤ correctionSigma 40 q a t beta :=
          correctionSigma_nonneg (by norm_num) hq.1 a t beta
        have hσsq : Real.sqrt (correctionSigma 40 q a t beta) ^ 2 =
            correctionSigma 40 q a t beta := Real.sq_sqrt hσnn
        have hlow : sigmaLowerConstant q * Real.sin beta ^ 2 ≤
            correctionSigma 40 q a t beta := correctionSigma_lower hq hcond
        unfold errorKernel
        rw [if_pos hmem, div_pow, mul_pow, hσsq]
        by_cases hsin : Real.sin beta = 0
        · rw [hM₀]
          simp [hsin]
        · have hX : 0 < Real.sin beta ^ 2 := by positivity
          have hσpos : 0 < correctionSigma 40 q a t beta := by nlinarith
          rw [hM₀, show ((s : ℝ) ^ 2) ^ 2 = s ^ 4 by ring,
            div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [mul_le_mul_of_nonneg_left hlow (mul_nonneg hX.le hs4.le)]
      · have hmem' : t ∉ {t : ℝ | -s + t - p₂ ∈ correctionInterval q a t beta} := hmem
        rw [if_neg hmem']
        unfold errorKernel
        rw [if_neg hmem]
        norm_num
    have hint : Integrable
        (fun t : ℝ => if t ∈ {t : ℝ |
          -s + t - p₂ ∈ correctionInterval q a t beta} then M₀ else 0)
        (volume.restrict torus) := by
      refine integrableOn_torus_of_bounded
        (Measurable.ite hset measurable_const measurable_const) (C := M₀) ?_
      intro t
      split_ifs
      · rw [abs_of_nonneg hM₀nn]
      · rw [abs_zero]; exact hM₀nn
    have hsub : {t : ℝ | -s + t - p₂ ∈ correctionInterval q a t beta} ⊆
        Set.Icc 0 (s / (4 * q.K)) := by
      intro t ht
      obtain ⟨hcond, hsupp, -⟩ := errorIntegrand_support hq ha hp₂ ht
      have hdelta : 0 < q.delta a := delta_pos hq ha
      have htK : q.K * q.delta a ≤ t := hcond.1.1
      have ht0 : 0 ≤ t := le_trans (by positivity) htK
      refine ⟨ht0, ?_⟩
      rw [le_div_iff₀ (by positivity)]
      nlinarith [abs_nonneg beta]
    calc torusIntegral (fun t : ℝ => errorKernel q a p₂ s beta t ^ 2)
        ≤ torusIntegral (fun t : ℝ =>
            if t ∈ {t : ℝ | -s + t - p₂ ∈ correctionInterval q a t beta} then M₀
            else 0) :=
          torusIntegral_mono' (fun t => sq_nonneg _) hint hpt
      _ ≤ (2 * Real.pi)⁻¹ * (M₀ * (s / (4 * q.K) - 0)) :=
          torusIntegral_indicator_const_le hset hsub (by positivity) hM₀nn
      _ = errorSMajorant q beta s := by
          unfold errorSMajorant
          rw [if_pos hA, hM₀]
          field_simp
          ring
  · have hzero : ∀ t : ℝ, errorKernel q a p₂ s beta t = 0 := by
      intro t
      unfold errorKernel
      rw [if_neg]
      intro hmem
      obtain ⟨hcond, hsupp, -⟩ := errorIntegrand_support hq ha hp₂ hmem
      have hdelta : 0 < q.delta a := delta_pos hq ha
      have htK : q.K * q.delta a ≤ t := hcond.1.1
      have ht0 : 0 ≤ t := le_trans (by positivity) htK
      exact hA (by nlinarith [abs_nonneg beta])
    have : (fun t : ℝ => errorKernel q a p₂ s beta t ^ 2) = fun _ : ℝ => (0 : ℝ) := by
      funext t; rw [hzero t]; ring
    rw [this, torusIntegral_const']
    exact errorSMajorant_nonneg hq beta s


theorem errorKernelConstant_pos {q : Parameters} (hq : q.Admissible) :
    0 < errorKernelConstant q := by
  have hK : 0 < q.K := K_pos hq
  have hrho : 0 < q.rho := rho_pos hq
  unfold errorKernelConstant
  positivity

theorem errorSMajorant_measurable (q : Parameters) (beta : ℝ) :
    Measurable (fun s : ℝ => errorSMajorant q beta s) := by
  unfold errorSMajorant
  refine Measurable.ite (measurableSet_le measurable_const measurable_id) ?_
    measurable_const
  fun_prop

theorem errorSMajorant_le {q : Parameters} (hq : q.Admissible) {beta : ℝ}
    (hbeta : beta ≠ 0) (s : ℝ) :
    errorSMajorant q beta s ≤
      (2 * Real.pi)⁻¹ * (Real.sin beta ^ 2 / (sigmaLowerConstant q * (4 * q.K))) *
        (((4 * q.K * |beta|) ^ 3)⁻¹) := by
  have hK : 0 < q.K := K_pos hq
  have hc : 0 < sigmaLowerConstant q := sigmaLowerConstant_pos hq
  have hbabs : 0 < |beta| := abs_pos.2 hbeta
  have hA : 0 < 4 * q.K * |beta| := by positivity
  have hD : (0 : ℝ) ≤ (2 * Real.pi)⁻¹ *
      (Real.sin beta ^ 2 / (sigmaLowerConstant q * (4 * q.K))) := by
    have := Real.pi_pos
    positivity
  unfold errorSMajorant
  split_ifs with h
  · refine mul_le_mul_of_nonneg_left ?_ hD
    have hs : 0 < s := lt_of_lt_of_le hA h
    refine inv_anti₀ (by positivity) ?_
    exact pow_le_pow_left₀ hA.le h 3
  · positivity

/-- Integrating the `s`-majorant, `manuscript.tex:1386-1393`. -/
theorem errorSMajorant_integral_le {q : Parameters} (hq : q.Admissible) {beta : ℝ}
    (hbeta : beta ≠ 0) :
    torusIntegral (fun s : ℝ => errorSMajorant q beta s) ≤
      errorKernelConstant q := by
  have hK : 0 < q.K := K_pos hq
  have hrho : 0 < q.rho := rho_pos hq
  have hpi : 0 < Real.pi := Real.pi_pos
  have hc : 0 < sigmaLowerConstant q := sigmaLowerConstant_pos hq
  have hbabs : 0 < |beta| := abs_pos.2 hbeta
  have hA : 0 < 4 * q.K * |beta| := by positivity
  have hB2 : (0 : ℝ) < beta ^ 2 := by positivity
  set D : ℝ := (2 * Real.pi)⁻¹ *
    (Real.sin beta ^ 2 / (sigmaLowerConstant q * (4 * q.K))) with hDdef
  have hD : 0 ≤ D := by rw [hDdef]; positivity
  have hsplit : torusIntegral (fun s : ℝ => errorSMajorant q beta s) =
      D * torusIntegral (fun s : ℝ =>
        if 4 * q.K * |beta| ≤ s then (s ^ 3)⁻¹ else 0) := by
    rw [← torusIntegral_smul_left]
    congr 1
    funext s
    unfold errorSMajorant
    rw [hDdef]
    split_ifs <;> ring
  rw [hsplit]
  have h2 := torusIntegral_indicator_inv_cube_le hA
  have hstep : D * torusIntegral (fun s : ℝ =>
      if 4 * q.K * |beta| ≤ s then (s ^ 3)⁻¹ else 0) ≤
      D * ((2 * Real.pi)⁻¹ * (1 / (2 * (4 * q.K * |beta|) ^ 2))) :=
    mul_le_mul_of_nonneg_left h2 hD
  refine hstep.trans ?_
  have hkey : D * ((2 * Real.pi)⁻¹ * (1 / (2 * (4 * q.K * |beta|) ^ 2))) =
      Real.sin beta ^ 2 / beta ^ 2 * (45 / (16 * Real.pi * q.K ^ 3 * q.rho)) := by
    rw [hDdef]
    unfold sigmaLowerConstant
    rw [mul_pow, mul_pow, sq_abs]
    field_simp
    ring
  rw [hkey]
  have h3 : Real.sin beta ^ 2 / beta ^ 2 ≤ 1 := by
    rw [div_le_one hB2]
    exact sin_sq_le_sq beta
  have h4 : (0 : ℝ) < 45 / (16 * Real.pi * q.K ^ 3 * q.rho) := by positivity
  calc Real.sin beta ^ 2 / beta ^ 2 * (45 / (16 * Real.pi * q.K ^ 3 * q.rho))
      ≤ 1 * (45 / (16 * Real.pi * q.K ^ 3 * q.rho)) :=
        mul_le_mul_of_nonneg_right h3 h4.le
    _ = 45 / (16 * Real.pi * q.K ^ 3 * q.rho) := one_mul _
    _ ≤ errorKernelConstant q := by
        unfold errorKernelConstant
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have hKr : (0 : ℝ) < q.K ^ 3 * q.rho := mul_pos (pow_pos hK 3) hrho
        nlinarith [mul_nonneg (by linarith [Real.two_le_pi] :
          (0 : ℝ) ≤ 48 * Real.pi - 45) hKr.le]

theorem errorU_nonneg {q : Parameters} (hq : q.Admissible) (a p₂ s beta : ℝ) :
    0 ≤ errorU q a p₂ s beta := by
  unfold errorU
  refine mul_nonneg (sq_nonneg _) (torusIntegral_nonneg' ?_)
  intro t
  split_ifs
  · exact mul_nonneg (correctionV_nonneg hq a t beta)
      (inv_nonneg.2 (multiplier_pos (by norm_num) hq.1 _).le)
  · exact le_rfl

/-! ### Step 3 of Lemma 5.4 -/

/-- The bound at a fixed column frequency `β`. -/
theorem errorHMinusSq_inner_le {q : Parameters} (hq : q.Admissible)
    {a p₂ : ℝ} (ha : 0 ≤ a) (hp₂ : |p₂| ≤ a) (beta : ℝ) :
    torusIntegral (fun s : ℝ =>
        if 0 < s then
          mixedHMinusWeight q (-s) beta * errorU q a p₂ s beta ^ 2 else 0)
      ≤ errorKernelConstant q *
        torusIntegral (fun t : ℝ =>
          correctionSigma 40 q a t beta * correctionV 40 q a t beta ^ 2) := by
  have hK : 0 < q.K := K_pos hq
  have hCpos : 0 < errorKernelConstant q := errorKernelConstant_pos hq
  set E : ℝ := torusIntegral (fun t : ℝ =>
    correctionSigma 40 q a t beta * correctionV 40 q a t beta ^ 2) with hEdef
  have hEnn : 0 ≤ E := by
    rw [hEdef]
    exact torusIntegral_nonneg' fun t => mul_nonneg
      (correctionSigma_nonneg (by norm_num) hq.1 a t beta) (sq_nonneg _)
  have hEphi : torusIntegral (fun t : ℝ => errorPhi q a t beta ^ 2) = E := by
    rw [hEdef]
    congr 1
    funext t
    exact errorPhi_sq hq a t beta
  have hmwnn : ∀ s : ℝ, 0 ≤ mixedHMinusWeight q (-s) beta := by
    intro s
    unfold mixedHMinusWeight
    have := mixed_denominator_pos hq.1 (-s) beta
    positivity
  by_cases hsin : Real.sin beta = 0
  · have hzero : (fun s : ℝ =>
        if 0 < s then
          mixedHMinusWeight q (-s) beta * errorU q a p₂ s beta ^ 2 else 0) =
        fun _ : ℝ => (0 : ℝ) := by
      funext s
      have hU : errorU q a p₂ s beta = 0 := by
        unfold errorU
        rw [hsin]
        ring
      rw [hU]
      split_ifs <;> ring
    rw [hzero, torusIntegral_const']
    positivity
  · have hbeta : beta ≠ 0 := by
      intro h
      rw [h, Real.sin_zero] at hsin
      exact hsin rfl
    have hmajint : Integrable (fun s : ℝ => errorSMajorant q beta s * E)
        (volume.restrict torus) := by
      refine integrableOn_torus_of_bounded
        ((errorSMajorant_measurable q beta).mul_const E)
        (C := ((2 * Real.pi)⁻¹ *
          (Real.sin beta ^ 2 / (sigmaLowerConstant q * (4 * q.K))) *
            (((4 * q.K * |beta|) ^ 3)⁻¹)) * |E|) ?_
      intro s
      rw [abs_mul]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg E)
      rw [abs_of_nonneg (errorSMajorant_nonneg hq beta s)]
      exact errorSMajorant_le hq hbeta s
    have hpt : ∀ s ∈ torus,
        (if 0 < s then
          mixedHMinusWeight q (-s) beta * errorU q a p₂ s beta ^ 2 else 0) ≤
        errorSMajorant q beta s * E := by
      intro s hstorus
      by_cases hs : 0 < s
      · rw [if_pos hs]
        have hspi : s ≤ Real.pi := hstorus.2
        have hRsq : Real.sqrt (mixedHMinusWeight q (-s) beta) ^ 2 =
            mixedHMinusWeight q (-s) beta := Real.sq_sqrt (hmwnn s)
        have hprod : mixedHMinusWeight q (-s) beta * errorU q a p₂ s beta ^ 2 =
            (Real.sqrt (mixedHMinusWeight q (-s) beta) *
              errorU q a p₂ s beta) ^ 2 := by
          rw [mul_pow, hRsq]
        have hle := sqrt_weight_mul_errorU_le hq ha hp₂ hs hspi (beta := beta)
        have hnn : 0 ≤ Real.sqrt (mixedHMinusWeight q (-s) beta) *
            errorU q a p₂ s beta :=
          mul_nonneg (Real.sqrt_nonneg _) (errorU_nonneg hq a p₂ s beta)
        have hsqle : (Real.sqrt (mixedHMinusWeight q (-s) beta) *
            errorU q a p₂ s beta) ^ 2 ≤
            (torusIntegral fun t : ℝ =>
              errorKernel q a p₂ s beta t * errorPhi q a t beta) ^ 2 :=
          pow_le_pow_left₀ hnn hle 2
        have hcs := torusIntegral_kernel_sq_le
          (k := fun t : ℝ => errorKernel q a p₂ s beta t)
          (g := fun t : ℝ => errorPhi q a t beta)
          (HS := errorSMajorant q beta s) (E := E)
          (errorKernel_sq_integrable hq ha hp₂ hs)
          (errorPhi_sq_integrable hq a beta)
          (errorKernel_sq_integral_le hq ha hp₂ hs) (le_of_eq hEphi) hEnn
        rw [hprod]
        linarith
      · rw [if_neg hs]
        exact mul_nonneg (errorSMajorant_nonneg hq beta s) hEnn
    calc torusIntegral (fun s : ℝ =>
          if 0 < s then
            mixedHMinusWeight q (-s) beta * errorU q a p₂ s beta ^ 2 else 0)
        ≤ torusIntegral (fun s : ℝ => errorSMajorant q beta s * E) := by
          refine torusIntegral_mono_on ?_ hmajint hpt
          intro s _
          split_ifs
          · exact mul_nonneg (hmwnn s) (sq_nonneg _)
          · exact le_rfl
      _ = E * torusIntegral (fun s : ℝ => errorSMajorant q beta s) := by
          rw [← torusIntegral_smul_left]
          congr 1
          funext s
          ring
      _ ≤ E * errorKernelConstant q :=
          mul_le_mul_of_nonneg_left (errorSMajorant_integral_le hq hbeta) hEnn
      _ = errorKernelConstant q * E := mul_comm _ _

theorem correctionSigmaEnergy_inner_nonneg {q : Parameters} (hq : q.Admissible)
    (a beta : ℝ) :
    0 ≤ torusIntegral (fun t : ℝ =>
      correctionSigma 40 q a t beta * correctionV 40 q a t beta ^ 2) :=
  torusIntegral_nonneg' fun t => mul_nonneg
    (correctionSigma_nonneg (by norm_num) hq.1 a t beta) (sq_nonneg _)

theorem correctionSigmaEnergy_inner_le {q : Parameters} (hq : q.Admissible)
    (a beta : ℝ) :
    torusIntegral (fun t : ℝ =>
      correctionSigma 40 q a t beta * correctionV 40 q a t beta ^ 2) ≤
      (40 * q.lambda)⁻¹ * (q.lambda⁻¹) ^ 2 := by
  have hbd : ∀ t : ℝ,
      correctionSigma 40 q a t beta * correctionV 40 q a t beta ^ 2 ≤
        (40 * q.lambda)⁻¹ * (q.lambda⁻¹) ^ 2 := by
    intro t
    have h1 := correctionSigma_le_inv hq a t beta
    have h2 := correctionV_le_inv hq a t beta
    have h3 := correctionV_nonneg hq a t beta
    have h4 := correctionSigma_nonneg (by norm_num : (0:ℝ) < 40) hq.1 a t beta
    have h5 : correctionV 40 q a t beta ^ 2 ≤ (q.lambda⁻¹) ^ 2 :=
      pow_le_pow_left₀ h3 h2 2
    have h6 : (0 : ℝ) ≤ (q.lambda⁻¹) ^ 2 := sq_nonneg _
    nlinarith
  have := torusIntegral_mono' (f := fun t : ℝ =>
      correctionSigma 40 q a t beta * correctionV 40 q a t beta ^ 2)
    (g := fun _ : ℝ => (40 * q.lambda)⁻¹ * (q.lambda⁻¹) ^ 2)
    (fun t => mul_nonneg (correctionSigma_nonneg (by norm_num) hq.1 a t beta)
      (sq_nonneg _))
    (integrable_const _) hbd
  simpa [torusIntegral_const'] using this

theorem correctionSigmaEnergy_inner_measurable (q : Parameters) (a : ℝ) :
    Measurable (fun beta : ℝ => torusIntegral (fun t : ℝ =>
      correctionSigma 40 q a t beta * correctionV 40 q a t beta ^ 2)) := by
  set F : ℝ → ℝ → ℝ := fun beta t =>
    correctionSigma 40 q a t beta * correctionV 40 q a t beta ^ 2 with hFdef
  have hF : Measurable (Function.uncurry F) := by
    have hunc : Function.uncurry F = fun z : ℝ × ℝ =>
        correctionSigma 40 q a z.2 z.1 * correctionV 40 q a z.2 z.1 ^ 2 := rfl
    rw [hunc]
    have hswap : Measurable (Prod.swap : ℝ × ℝ → ℝ × ℝ) := measurable_swap
    have hsig0 := (correctionSigma_measurable 40 q a).comp hswap
    have hv0 := (correctionV_measurable 40 q a).comp hswap
    have hsig : Measurable (fun z : ℝ × ℝ => correctionSigma 40 q a z.2 z.1) := hsig0
    have hv : Measurable (fun z : ℝ × ℝ => correctionV 40 q a z.2 z.1) := hv0
    exact hsig.mul (hv.pow_const 2)
  have hinner : StronglyMeasurable (fun beta : ℝ =>
      ∫ t, F beta t ∂(volume.restrict torus)) :=
    hF.stronglyMeasurable.integral_prod_right
  simp only [torusIntegral, smul_eq_mul]
  exact hinner.measurable.const_mul _

/-- **Step 3 of Lemma 5.4**, equation `(ebound)` of `manuscript.tex:1394-1398`:
the squared `H⁻¹` norm of the error term at negative row frequencies is at
most a constant times the multiplier energy `∫∫ σ|v|²`. -/
theorem errorHMinusSq_le {q : Parameters} (hq : q.Admissible) {a p₂ : ℝ}
    (ha : 0 ≤ a) (hp₂ : |p₂| ≤ a) :
    errorHMinusSq q a p₂ ≤
      errorKernelConstant q * correctionSigmaEnergyBeta q a := by
  have hCpos : 0 < errorKernelConstant q := errorKernelConstant_pos hq
  have hmajint : Integrable (fun beta : ℝ => errorKernelConstant q *
      torusIntegral (fun t : ℝ =>
        correctionSigma 40 q a t beta * correctionV 40 q a t beta ^ 2))
      (volume.restrict torus) := by
    refine integrableOn_torus_of_bounded
      ((correctionSigmaEnergy_inner_measurable q a).const_mul _)
      (C := errorKernelConstant q * ((40 * q.lambda)⁻¹ * (q.lambda⁻¹) ^ 2)) ?_
    intro beta
    rw [abs_of_nonneg (mul_nonneg hCpos.le
      (correctionSigmaEnergy_inner_nonneg hq a beta))]
    exact mul_le_mul_of_nonneg_left (correctionSigmaEnergy_inner_le hq a beta)
      hCpos.le
  unfold errorHMinusSq correctionSigmaEnergyBeta
  calc torusIntegral (fun beta : ℝ =>
        torusIntegral (fun s : ℝ =>
          if 0 < s then
            mixedHMinusWeight q (-s) beta * errorU q a p₂ s beta ^ 2 else 0))
      ≤ torusIntegral (fun beta : ℝ => errorKernelConstant q *
          torusIntegral (fun t : ℝ =>
            correctionSigma 40 q a t beta * correctionV 40 q a t beta ^ 2)) := by
        refine torusIntegral_mono' ?_ hmajint
          (errorHMinusSq_inner_le hq ha hp₂)
        intro beta
        refine torusIntegral_nonneg' ?_
        intro s
        split_ifs
        · refine mul_nonneg ?_ (sq_nonneg _)
          unfold mixedHMinusWeight
          have := mixed_denominator_pos hq.1 (-s) beta
          positivity
        · exact le_rfl
    _ = errorKernelConstant q * torusIntegral (fun beta : ℝ =>
          torusIntegral (fun t : ℝ =>
            correctionSigma 40 q a t beta * correctionV 40 q a t beta ^ 2)) :=
        torusIntegral_smul_left _ _

/-! ### The two orders of integration -/

theorem correctionSigmaEnergy_uncurry_measurable (q : Parameters) (a : ℝ) :
    Measurable (Function.uncurry (fun beta t : ℝ =>
      correctionSigma 40 q a t beta * correctionV 40 q a t beta ^ 2)) := by
  have hunc : Function.uncurry (fun beta t : ℝ =>
      correctionSigma 40 q a t beta * correctionV 40 q a t beta ^ 2) =
      fun z : ℝ × ℝ =>
        correctionSigma 40 q a z.2 z.1 * correctionV 40 q a z.2 z.1 ^ 2 := rfl
  rw [hunc]
  have hswap : Measurable (Prod.swap : ℝ × ℝ → ℝ × ℝ) := measurable_swap
  have hsig0 := (correctionSigma_measurable 40 q a).comp hswap
  have hv0 := (correctionV_measurable 40 q a).comp hswap
  have hsig : Measurable (fun z : ℝ × ℝ => correctionSigma 40 q a z.2 z.1) := hsig0
  have hv : Measurable (fun z : ℝ × ℝ => correctionV 40 q a z.2 z.1) := hv0
  exact hsig.mul (hv.pow_const 2)

/-- Tonelli for the bounded nonnegative density `σ|v|²`. -/
theorem correctionSigmaEnergyBeta_swap {q : Parameters} (hq : q.Admissible)
    (a : ℝ) :
    correctionSigmaEnergyBeta q a =
      torusIntegral (fun r : ℝ => torusIntegral (fun beta : ℝ =>
        correctionSigma 40 q a r beta * correctionV 40 q a r beta ^ 2)) := by
  set F : ℝ → ℝ → ℝ := fun beta t =>
    correctionSigma 40 q a t beta * correctionV 40 q a t beta ^ 2 with hFdef
  have hbd : ∀ z : ℝ × ℝ,
      ‖Function.uncurry F z‖ ≤ (40 * q.lambda)⁻¹ * (q.lambda⁻¹) ^ 2 := by
    intro z
    have h1 := correctionSigma_le_inv hq a z.2 z.1
    have h2 := correctionV_le_inv hq a z.2 z.1
    have h3 := correctionV_nonneg hq a z.2 z.1
    have h4 := correctionSigma_nonneg (by norm_num : (0:ℝ) < 40) hq.1 a z.2 z.1
    have h5 : correctionV 40 q a z.2 z.1 ^ 2 ≤ (q.lambda⁻¹) ^ 2 :=
      pow_le_pow_left₀ h3 h2 2
    have hnn : (0 : ℝ) ≤ correctionSigma 40 q a z.2 z.1 *
        correctionV 40 q a z.2 z.1 ^ 2 := mul_nonneg h4 (sq_nonneg _)
    show ‖correctionSigma 40 q a z.2 z.1 * correctionV 40 q a z.2 z.1 ^ 2‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    nlinarith [sq_nonneg (q.lambda⁻¹)]
  have hint : Integrable (Function.uncurry F)
      ((volume.restrict torus).prod (volume.restrict torus)) :=
    Integrable.mono' (integrable_const _)
      (correctionSigmaEnergy_uncurry_measurable q a).aestronglyMeasurable
      (Filter.Eventually.of_forall hbd)
  have hswap := integral_integral_swap (μ := volume.restrict torus)
    (ν := volume.restrict torus) (f := F) hint
  unfold correctionSigmaEnergyBeta
  simp only [torusIntegral, smul_eq_mul]
  rw [integral_const_mul, integral_const_mul, hswap]

/-- Step 3 of Lemma 5.4 with the `σ`-energy written in the row-frequency
order used by `Manhattan.Glue.correctionSigmaEnergy`. -/
theorem errorHMinusSq_le_rowOrder {q : Parameters} (hq : q.Admissible)
    {a p₂ : ℝ} (ha : 0 ≤ a) (hp₂ : |p₂| ≤ a) :
    errorHMinusSq q a p₂ ≤ errorKernelConstant q *
      torusIntegral (fun r : ℝ => torusIntegral (fun beta : ℝ =>
        correctionSigma 40 q a r beta * correctionV 40 q a r beta ^ 2)) := by
  rw [← correctionSigmaEnergyBeta_swap hq a]
  exact errorHMinusSq_le hq ha hp₂

end

end Manhattan.Estimates