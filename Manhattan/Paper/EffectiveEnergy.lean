import Manhattan.Paper.ParityTransport
import Manhattan.V4.SharpMove1
import Manhattan.V4.SplitConstant
import Manhattan.Paper.Constant.Move3

/-!
# `lem:effective-energy` with the constant `16`, and `prop:frequency` with `2048`

`lem:effective-energy` (`paper/arxiv/main.tex:951-1033`) bounds the resolvent
quadratic form by `(1 - s∫φ)²/H₀ + 16 ∫ q φ²`.  The proof, followed here:

* orthogonality of the Walsh degrees, and of the two-row and mixed sectors of
  degree two, splits the objective of `eq:uncancelled` exactly
  (`objective_eq_sectors`): no parallelogram factor is paid;
* `eq:degree-one-cost` bounds the degree-one energy and the two-row sector by a
  multiple of `∫ q φ²` (`degreeOne_cost_le_sharp`, `twoRow_cost_le_sharp`;
  their sum is `15/4 ∫ q φ²`, below the paper's `5`);
* `lem:parity` bounds the degree-three cost and the mixed sector together by
  `∫∫ w²/W` (`Manhattan.Paper.sectorForms_rawWalsh_le` and `parityCost_eq`);
* `eq:beta` bounds `∫ dm(β)/W` by `(π^{5/2}+π)/(2 |r| √(log(1/|r|)))`
  (`Manhattan.V4.betaColumnBound_split` at `M = 4(δ + |r| + |r'| + |β|)`), and
  `(π^{5/2}+π)/2 < 11`.

The competitor is the parity competitor of `Manhattan/V4/Move1.lean` built
from the profile `φ = t/q` on `Γ_δ` of `eq:Z`, the family that `prop:frequency`
uses.  The output is `move2Supply_sixteen`, the bound `eq:optimized`
`r_λ(p) ≤ 1/(H₀ + s² Z_δ/16)`, and `frequencyBound_2048`, `prop:frequency`
with the constant `2048`.
-/

open scoped lp
open MeasureTheory Set UnitAddTorus
open Manhattan Manhattan.Glue Manhattan.V4.Frequency
open LatticeProb.Analysis

namespace Manhattan.Paper

noncomputable section

/-! ### Orthogonality of the sectors -/

/-- Vectors of different Walsh degree are orthogonal. -/
theorem inner_eq_zero_of_mem_walshDegree {m n : ℕ} (hmn : m ≠ n) {x y : WalshL2}
    (hx : x ∈ Manhattan.walshDegree n) (hy : y ∈ Manhattan.walshDegree m) :
    inner ℂ x y = 0 := by
  classical
  have hspan :
      Submodule.span ℂ {f | ∃ T : Finset LineIndex, T.card = m ∧ f = Manhattan.walshL2 T} ≤
        LinearMap.ker ((innerSL ℂ x : WalshL2 →L[ℂ] ℂ) : WalshL2 →ₗ[ℂ] ℂ) := by
    rw [Submodule.span_le]
    rintro _ ⟨T, hT, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
      innerSL_apply_apply]
    rw [← InnerProductSpace.conj_inner_symm,
      inner_walshL2_eq_zero_of_mem_walshDegree hx (by rw [hT]; exact hmn), map_zero]
  have hclosed : IsClosed
      ((LinearMap.ker ((innerSL ℂ x : WalshL2 →L[ℂ] ℂ) : WalshL2 →ₗ[ℂ] ℂ)) : Set WalshL2) :=
    ContinuousLinearMap.isClosed_ker (innerSL ℂ x)
  exact Submodule.topologicalClosure_minimal _ hspan hclosed hy

/-- `H⁻¹` preserves the Walsh degree. -/
theorem hInverse_mem_walshDegree {lam : ℝ} (hlam : 0 < lam) (p : Fin 2 → ℝ) (n : ℕ)
    {v : WalshL2} (hv : v ∈ Manhattan.walshDegree n) :
    ((concreteFiberEnvironment.dissipativeSkewPair p).hEquiv hlam).symm v ∈
      Manhattan.walshDegree n := by
  have hv' : v ∈ (Manhattan.walshDegree n : Set WalshL2) := hv
  rw [walshDegree_eq_range] at hv'
  obtain ⟨c, rfl⟩ := hv'
  obtain ⟨c', hc'⟩ := (coeffH_bijective n hlam p).2 c
  have h : ((concreteFiberEnvironment.dissipativeSkewPair p).hEquiv hlam).symm
      (homogeneousWalshSynthesis n c) = homogeneousWalshSynthesis n c' := by
    rw [ContinuousLinearEquiv.symm_apply_eq]
    show homogeneousWalshSynthesis n c =
      (concreteFiberEnvironment.dissipativeSkewPair p).H lam (homogeneousWalshSynthesis n c')
    rw [fiberH_homogeneousWalshSynthesis, hc']
  rw [h]
  exact homogeneousWalshSynthesis_mem_degree n c'

/-- **The energy is additive across Walsh degrees.** -/
theorem hEnergy_add_of_walshDegree (lam : ℝ) (p : Fin 2 → ℝ) {m n : ℕ} (hmn : m ≠ n)
    {u v : WalshL2} (hu : u ∈ Manhattan.walshDegree m) (hv : v ∈ Manhattan.walshDegree n) :
    (concreteFiberEnvironment.dissipativeSkewPair p).hEnergy lam (u + v) =
      (concreteFiberEnvironment.dissipativeSkewPair p).hEnergy lam u +
        (concreteFiberEnvironment.dissipativeSkewPair p).hEnergy lam v := by
  have hHu := fiberH_mem_walshDegree' m lam p hu
  have hHv := fiberH_mem_walshDegree' n lam p hv
  have e1 : inner ℂ ((concreteFiberEnvironment.dissipativeSkewPair p).H lam u) v = 0 :=
    inner_eq_zero_of_mem_walshDegree hmn.symm hHu hv
  have e2 : inner ℂ ((concreteFiberEnvironment.dissipativeSkewPair p).H lam v) u = 0 :=
    inner_eq_zero_of_mem_walshDegree hmn hHv hu
  simp only [DissipativeSkewPair.hEnergy, map_add, inner_add_left, inner_add_right, e1, e2,
    add_zero, zero_add]

/-- **The dual energy is additive across Walsh degrees.** -/
theorem hMinusEnergy_add_of_walshDegree {lam : ℝ} (hlam : 0 < lam) (p : Fin 2 → ℝ)
    {m n : ℕ} (hmn : m ≠ n) {u v : WalshL2} (hu : u ∈ Manhattan.walshDegree m)
    (hv : v ∈ Manhattan.walshDegree n) :
    (concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hlam (u + v) =
      (concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hlam u +
        (concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hlam v := by
  have hiu := hInverse_mem_walshDegree hlam p m hu
  have hiv := hInverse_mem_walshDegree hlam p n hv
  have e1 : inner ℂ u (((concreteFiberEnvironment.dissipativeSkewPair p).hEquiv hlam).symm v) =
      0 := inner_eq_zero_of_mem_walshDegree hmn.symm hu hiv
  have e2 : inner ℂ v (((concreteFiberEnvironment.dissipativeSkewPair p).hEquiv hlam).symm u) =
      0 := inner_eq_zero_of_mem_walshDegree hmn hv hiu
  simp only [DissipativeSkewPair.hMinusEnergy, map_add, inner_add_left, inner_add_right, e1, e2,
    add_zero, zero_add]

/-- **The dual energy is additive across the two-row and mixed sectors.** -/
theorem hMinusEnergy_type11_add_type12 {lam : ℝ} (hlam : 0 < lam) (p : Fin 2 → ℝ)
    (a : ℓ²(Manhattan.Type11Index, ℂ)) (b : ℓ²(Manhattan.Type12Index, ℂ)) :
    (concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hlam
        (Manhattan.type11WalshSynthesis a + Manhattan.type12WalshSynthesis b) =
      (concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hlam
          (Manhattan.type11WalshSynthesis a) +
        (concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hlam
          (Manhattan.type12WalshSynthesis b) := by
  classical
  have hne : (type11Pattern : Fin 2 → Axis) ≠ type12Pattern := by decide
  rw [type11WalshSynthesis_eq_homogeneous, type12WalshSynthesis_eq_homogeneous, ← map_add,
    hMinusEnergy_homogeneousWalshSynthesis 2 hlam p, hMinusEnergy_homogeneousWalshSynthesis 2 hlam p,
    hMinusEnergy_homogeneousWalshSynthesis 2 hlam p, map_add, lineIndexFourier_type11Extend,
    lineIndexFourier_type12Extend, tsum_fintype, tsum_fintype, tsum_fintype,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [show ((lp.single 2 type11Pattern (type11FreqFun a) +
      lp.single 2 type12Pattern (type12FreqFun b) : LineFreqL2 2) σ) =
      (lp.single 2 type11Pattern (type11FreqFun a) : LineFreqL2 2) σ +
        (lp.single 2 type12Pattern (type12FreqFun b) : LineFreqL2 2) σ from rfl]
  by_cases h1 : σ = type11Pattern
  · subst h1
    rw [lp.single_apply_self, lp.single_apply_ne _ _ _ hne, add_zero,
      integral_weight_zero_lp 2 _, add_zero]
  · by_cases h2 : σ = type12Pattern
    · subst h2
      rw [lp.single_apply_self, lp.single_apply_ne _ _ _ (Ne.symm hne), zero_add,
        integral_weight_zero_lp 2 _, zero_add]
    · rw [lp.single_apply_ne _ _ _ h1, lp.single_apply_ne _ _ _ h2, add_zero,
        integral_weight_zero_lp 2 _, add_zero]

/-- **`eq:uncancelled` without loss.**  For `f` of degree one carrying only row
signs and `k` of type `112` with `(D₂*k)₁₁ = 0`, the objective of
`lem:variational-bound` is the uncancelled degree-zero term plus the four
summands of `eq:E`, the degree-two summand split into its two-row and mixed
sectors. -/
theorem objective_eq_sectors {lambda : ℝ} (hlambda : 0 < lambda)
    (p : Fin 2 → ℝ) {cc : ℝ} (c : Manhattan.RowLineCoefficient)
    (kc : ℓ²(Manhattan.Type112Index, ℂ))
    (hk : Manhattan.type112DStarTwoRow p kc = 0)
    (hc : inner ℂ (Manhattan.walshL2 ∅)
        (unnormalizedResidual p 1
          (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal c)
          (Manhattan.type112WalshSynthesis kc)) = ((cc : ℝ) : ℂ)) :
    (concreteFiberEnvironment.dissipativeSkewPair p).hEnergy lambda
        (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal c
          + Manhattan.type112WalshSynthesis kc)
      + (concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hlambda
          (Manhattan.walshL2 ∅ - concreteFiberA p
            (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal c
              + Manhattan.type112WalshSynthesis kc))
      = cc ^ 2 / (lambda + Operator.theta p)
        + (concreteFiberEnvironment.dissipativeSkewPair p).hEnergy lambda
            (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal c)
        + (concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hlambda
            (Manhattan.type11WalshSynthesis (Manhattan.type11WalshAnalysis
              (walshRaise p (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal c))))
        + (sectorHThreeForm lambda p (Manhattan.type112WalshSynthesis kc)
            + sectorDFourForm hlambda p (Manhattan.type112WalshSynthesis kc))
        + (concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hlambda
            (Manhattan.type12WalshSynthesis
              (Manhattan.type12WalshAnalysis (walshRaise p
                  (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal c))
                - Manhattan.type112DStarMixed p kc)) := by
  have hf : Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal c
      ∈ Manhattan.walshDegree 1 := axisDegreeOneSynthesis_mem_walshDegree _ c
  have hkk : Manhattan.type112WalshSynthesis kc ∈ Manhattan.walshDegree 3 :=
    Manhattan.type112WalshSynthesis_mem_degree kc
  have hres : unnormalizedResidual p 1
      (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal c)
      (Manhattan.type112WalshSynthesis kc)
      = Manhattan.walshL2 ∅ - concreteFiberA p
          (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal c
            + Manhattan.type112WalshSynthesis kc) := by
    rw [unnormalizedResidual, Complex.ofReal_one, one_smul]
  have hE := hEnergy_add_of_walshDegree lambda p (by norm_num : (1 : ℕ) ≠ 3) hf hkk
  have hsplit := V4.unnormalizedResidual_eq_three_sectors p 1 hf hkk hc
  rw [← hres, hsplit, V4.hMinusEnergy_empty_add hlambda p cc
      (V4.inner_empty_sector_sum _),
    hMinusEnergy_add_of_walshDegree hlambda p (by norm_num : (2 : ℕ) ≠ 4)
      (walshSectorComponent_card_mem_walshDegree 2 _)
      (walshSectorComponent_card_mem_walshDegree 4 _),
    hMinusEnergy_sector_two_residual, hMinusEnergy_sector_four_residual hlambda p 1 hf,
    walshSectorComponent_two_concreteFiberA_eq p c kc hk, hMinusEnergy_type11_add_type12, hE]
  have hH : sectorHThreeForm lambda p (Manhattan.type112WalshSynthesis kc)
      = (concreteFiberEnvironment.dissipativeSkewPair p).hEnergy lambda
        (Manhattan.type112WalshSynthesis kc) := rfl
  have hD : sectorDFourForm hlambda p (Manhattan.type112WalshSynthesis kc)
      = (concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy
        hlambda (walshSectorComponent (fun S => S.card = 4)
          (concreteFiberA p (Manhattan.type112WalshSynthesis kc))) := rfl
  rw [hH, hD]
  ring

/-! ### The degree-one cost, `eq:degree-one-cost` -/

open Manhattan.V4.Frequency in
/-- The degree-one energy density against the effective weight: `μ + d(r) ≤ 3r²/2
≤ ¾ q(r)` on `Γ_δ`. -/
theorem degreeOne_cost_le_sharp {mu delta r0 : ℝ} (hmu : 0 < mu) (hdelta : 0 < delta)
    (hdelta1 : delta ≤ 1) (hmud : mu ≤ delta ^ 2) (hr0 : r0 ≤ 1 / 4)
    {phi : ℝ → ℝ}
    (hsupp : ∀ r ∈ Estimates.torus, ¬ (Real.sqrt delta ≤ |r| ∧ |r| ≤ r0) → phi r = 0)
    (hint : Integrable (fun r => V4.Energy.effectiveWeight r * phi r ^ 2)
      (volume.restrict Estimates.torus)) :
    Estimates.torusIntegral (fun r => (mu + Estimates.dispersion r) * phi r ^ 2)
      ≤ 3 / 4 * Estimates.torusIntegral
          (fun r => V4.Energy.effectiveWeight r * phi r ^ 2) := by
  rw [← Estimates.torusIntegral_smul_left]
  refine Estimates.torusIntegral_mono_on ?_ (hint.const_mul (3 / 4)) ?_
  · intro x _
    have := Estimates.dispersion_nonneg x
    have : (0:ℝ) ≤ mu + Estimates.dispersion x := by linarith
    exact mul_nonneg this (sq_nonneg _)
  · intro x hx
    by_cases hmem : Real.sqrt delta ≤ |x| ∧ |x| ≤ r0
    · have hxpos : 0 < |x| := lt_of_lt_of_le (Real.sqrt_pos.2 hdelta) hmem.1
      have hx14 : |x| ≤ 1 / 4 := le_trans hmem.2 hr0
      have hdx : delta ≤ x ^ 2 := by
        rw [← sq_abs x]
        nlinarith [Real.sq_sqrt hdelta.le, Real.sqrt_nonneg delta, hmem.1]
      have hdd : delta ^ 2 ≤ delta := by nlinarith
      have hcos := Real.one_sub_sq_div_two_le_cos (x := x)
      have hdisp : Estimates.dispersion x ≤ x ^ 2 / 2 := by
        unfold Estimates.dispersion
        linarith
      have hq := V4.Energy.two_mul_sq_le_effectiveWeight hxpos hx14
      have h3 : mu + Estimates.dispersion x ≤ 3 / 4 * V4.Energy.effectiveWeight x := by
        linarith
      have := mul_le_mul_of_nonneg_right h3 (sq_nonneg (phi x))
      calc (mu + Estimates.dispersion x) * phi x ^ 2
          ≤ 3 / 4 * V4.Energy.effectiveWeight x * phi x ^ 2 := this
        _ = 3 / 4 * (V4.Energy.effectiveWeight x * phi x ^ 2) := by ring
    · rw [hsupp x hx hmem]
      simp

/-- `4 s²/√(μ(μ+2)) ≤ 6δ` when `s² ≤ 2μ` and `μ ≤ δ²`. -/
theorem four_sin_sq_lineResolvent_le {mu delta s : ℝ} (hmu : 0 < mu) (hdelta : 0 < delta)
    (hmud : mu ≤ delta ^ 2) (hs : s ^ 2 ≤ 2 * mu) :
    4 * (s ^ 2 / Real.sqrt (mu * (mu + 2))) ≤ 6 * delta := by
  have h2μ : Real.sqrt (2 * mu) ≤ Real.sqrt (mu * (mu + 2)) := Real.sqrt_le_sqrt (by nlinarith)
  have hs2 : 0 < Real.sqrt (2 * mu) := Real.sqrt_pos.2 (by linarith)
  have hsq : Real.sqrt (2 * mu) ^ 2 = 2 * mu := Real.sq_sqrt (by linarith)
  have hle : Real.sqrt (2 * mu) ≤ 3 / 2 * delta := by
    rw [show 3 / 2 * delta = Real.sqrt ((3 / 2 * delta) ^ 2) from
      (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have h1 : s ^ 2 / Real.sqrt (mu * (mu + 2)) ≤ 2 * mu / Real.sqrt (2 * mu) := by
    calc s ^ 2 / Real.sqrt (mu * (mu + 2)) ≤ 2 * mu / Real.sqrt (mu * (mu + 2)) :=
          div_le_div_of_nonneg_right hs (le_trans hs2.le h2μ)
      _ ≤ 2 * mu / Real.sqrt (2 * mu) :=
          div_le_div_of_nonneg_left (by linarith) hs2 h2μ
  have h2 : 2 * mu / Real.sqrt (2 * mu) = Real.sqrt (2 * mu) := by
    rw [div_eq_iff hs2.ne', ← sq, hsq]
  rw [h2] at h1
  linarith

open Manhattan.V4.Frequency in
/-- The two-row density `4 s² J(μ)` of `Manhattan.V4.hMinusEnergy_twoRow_le` against
the effective weight: it is at most `6δ ≤ 6r² ≤ 3 q(r)` on `Γ_δ`. -/
theorem twoRow_cost_le_sharp {mu delta r0 s : ℝ} (hmu : 0 < mu) (hdelta : 0 < delta)
    (hmud : mu ≤ delta ^ 2) (hs : s ^ 2 ≤ 2 * mu)
    (hr0 : r0 ≤ 1 / 4) {phi : ℝ → ℝ}
    (hsupp : ∀ r ∈ Estimates.torus, ¬ (Real.sqrt delta ≤ |r| ∧ |r| ≤ r0) → phi r = 0)
    (hint : Integrable (fun r => V4.Energy.effectiveWeight r * phi r ^ 2)
      (volume.restrict Estimates.torus)) :
    4 * (s ^ 2 / Real.sqrt (mu * (mu + 2))) * Estimates.torusIntegral (fun r => phi r ^ 2)
      ≤ 3 * Estimates.torusIntegral
          (fun r => V4.Energy.effectiveWeight r * phi r ^ 2) := by
  have hJ := four_sin_sq_lineResolvent_le hmu hdelta hmud hs
  have hJnn : (0:ℝ) ≤ 4 * (s ^ 2 / Real.sqrt (mu * (mu + 2))) := by positivity
  rw [← Estimates.torusIntegral_smul_left, ← Estimates.torusIntegral_smul_left]
  refine Estimates.torusIntegral_mono_on ?_ (hint.const_mul 3) ?_
  · intro x _
    exact mul_nonneg hJnn (sq_nonneg _)
  · intro x hx
    by_cases hmem : Real.sqrt delta ≤ |x| ∧ |x| ≤ r0
    · have hxpos : 0 < |x| := lt_of_lt_of_le (Real.sqrt_pos.2 hdelta) hmem.1
      have hx14 : |x| ≤ 1 / 4 := le_trans hmem.2 hr0
      have hdx : delta ≤ x ^ 2 := by
        rw [← sq_abs x]
        nlinarith [Real.sq_sqrt hdelta.le, Real.sqrt_nonneg delta, hmem.1]
      have hq := V4.Energy.two_mul_sq_le_effectiveWeight hxpos hx14
      have h4 : 4 * (s ^ 2 / Real.sqrt (mu * (mu + 2))) ≤ 3 * V4.Energy.effectiveWeight x := by
        linarith
      have := mul_le_mul_of_nonneg_right h4 (sq_nonneg (phi x))
      calc 4 * (s ^ 2 / Real.sqrt (mu * (mu + 2))) * phi x ^ 2
          ≤ 3 * V4.Energy.effectiveWeight x * phi x ^ 2 := this
        _ = 3 * (V4.Energy.effectiveWeight x * phi x ^ 2) := by ring
    · rw [hsupp x hx hmem]
      simp

/-! ### The parity cost, `eq:scalar-energy` -/

/-- **The completed square, integrated.**  At the minimizer `V = w/(B+σ)` the
degree-three density `σ V²` and the mixed residual `(w - σV)²/B` add up to
`w²/(B+σ)`, and integrate to `∫ w² ∫ dm(β)/(B+σ)`. -/
theorem parityCost_eq {kappa delta Kw : ℝ} {q : Estimates.Parameters}
    (hlam : 0 < q.lambda) (hkappa : 0 < kappa) (hdelta : 0 < delta)
    {w : ℝ → ℝ} (hmw : Measurable w) (hbw : ∀ r, |w r| ≤ Kw) :
    (Estimates.torusIntegral fun beta => Estimates.torusIntegral fun r =>
        V4.paritySigma kappa delta r beta
          * V4.parityV q kappa delta (fun r' _ => w r') r beta ^ 2)
      + (Estimates.torusIntegral fun r => Estimates.torusIntegral fun beta =>
        (w r - V4.paritySigma kappa delta r beta
            * V4.parityV q kappa delta (fun r' _ => w r') r beta) ^ 2
          / Estimates.correctionB q r beta)
      = Estimates.torusIntegral (fun r => w r ^ 2 * V4.parityFibreJ q kappa delta r) := by
  have hKw : 0 ≤ Kw := le_trans (abs_nonneg _) (hbw 0)
  have hBpos : ∀ r beta : ℝ, 0 < Estimates.correctionB q r beta :=
    fun r beta => lt_of_lt_of_le hlam (V4.correctionB_ge q r beta)
  have hsig : ∀ r beta : ℝ, 0 ≤ V4.paritySigma kappa delta r beta :=
    fun r beta => V4.paritySigma_nonneg hkappa hdelta r beta
  have hden : ∀ r beta : ℝ, q.lambda ≤
      Estimates.correctionB q r beta + V4.paritySigma kappa delta r beta :=
    fun r beta => V4.lambda_le_correctionB_add_paritySigma hkappa hdelta r beta
  have hnum : ∀ r, w r ^ 2 ≤ Kw ^ 2 := fun r => by
    nlinarith [hbw r, abs_nonneg (w r), sq_abs (w r)]
  have hquot : ∀ r beta : ℝ, w r ^ 2 / (Estimates.correctionB q r beta
      + V4.paritySigma kappa delta r beta) ≤ Kw ^ 2 / q.lambda := by
    intro r beta
    have hdp : 0 < Estimates.correctionB q r beta + V4.paritySigma kappa delta r beta :=
      lt_of_lt_of_le hlam (hden r beta)
    calc w r ^ 2 / (Estimates.correctionB q r beta + V4.paritySigma kappa delta r beta)
        ≤ Kw ^ 2 / (Estimates.correctionB q r beta + V4.paritySigma kappa delta r beta) :=
          div_le_div_of_nonneg_right (hnum r) hdp.le
      _ ≤ Kw ^ 2 / q.lambda := div_le_div_of_nonneg_left (sq_nonneg _) hlam (hden r beta)
  have hV : ∀ r beta : ℝ, V4.parityV q kappa delta (fun r' _ => w r') r beta
      = w r / (Estimates.correctionB q r beta + V4.paritySigma kappa delta r beta) :=
    fun r beta => rfl
  have hmB : Measurable fun z : ℝ × ℝ => Estimates.correctionB q z.1 z.2 := by
    unfold Estimates.correctionB Estimates.dispersion
    fun_prop
  have hmS : Measurable fun z : ℝ × ℝ => V4.paritySigma kappa delta z.1 z.2 :=
    V4.paritySigma_measurable kappa delta
  have hmV : Measurable fun z : ℝ × ℝ =>
      V4.parityV q kappa delta (fun r' _ => w r') z.1 z.2 :=
    (hmw.comp measurable_fst).div (hmB.add hmS)
  have hma : Measurable fun z : ℝ × ℝ => V4.paritySigma kappa delta z.1 z.2
      * V4.parityV q kappa delta (fun r' _ => w r') z.1 z.2 ^ 2 := hmS.mul (hmV.pow_const 2)
  have hmb : Measurable fun z : ℝ × ℝ => (w z.1 - V4.paritySigma kappa delta z.1 z.2
      * V4.parityV q kappa delta (fun r' _ => w r') z.1 z.2) ^ 2
        / Estimates.correctionB q z.1 z.2 :=
    (((hmw.comp measurable_fst).sub (hmS.mul hmV)).pow_const 2).div hmB
  have hba : ∀ r beta, |V4.paritySigma kappa delta r beta
      * V4.parityV q kappa delta (fun r' _ => w r') r beta ^ 2| ≤ Kw ^ 2 / q.lambda := by
    intro r beta
    have h := V4.v4_sigmaEnergy_le (w := w r) (hBpos r beta) (hsig r beta)
    rw [abs_of_nonneg (mul_nonneg (hsig r beta) (sq_nonneg _)), hV]
    exact h.trans (hquot r beta)
  have hbb : ∀ r beta, |(w r - V4.paritySigma kappa delta r beta
      * V4.parityV q kappa delta (fun r' _ => w r') r beta) ^ 2
        / Estimates.correctionB q r beta| ≤ Kw ^ 2 / q.lambda := by
    intro r beta
    have h := V4.v4_residual_le (w := w r) (hBpos r beta) (hsig r beta)
    rw [abs_of_nonneg (div_nonneg (sq_nonneg _) (hBpos r beta).le), hV]
    exact h.trans (hquot r beta)
  have hswapA := V4.torusIntegral_swap_of_bounded
    (F := fun r beta => V4.paritySigma kappa delta r beta
      * V4.parityV q kappa delta (fun r' _ => w r') r beta ^ 2) hma hba
  have hadd := torusIntegral₂_add
    (f := fun r beta => V4.paritySigma kappa delta r beta
      * V4.parityV q kappa delta (fun r' _ => w r') r beta ^ 2)
    (g := fun r beta => (w r - V4.paritySigma kappa delta r beta
      * V4.parityV q kappa delta (fun r' _ => w r') r beta) ^ 2
        / Estimates.correctionB q r beta) hma hba hmb hbb
  have hbab : ∀ r beta, |V4.paritySigma kappa delta r beta
      * V4.parityV q kappa delta (fun r' _ => w r') r beta ^ 2
      + (w r - V4.paritySigma kappa delta r beta
      * V4.parityV q kappa delta (fun r' _ => w r') r beta) ^ 2
        / Estimates.correctionB q r beta| ≤ Kw ^ 2 / q.lambda + Kw ^ 2 / q.lambda :=
    fun r beta => (abs_add_le _ _).trans (add_le_add (hba r beta) (hbb r beta))
  have hswapS := V4.torusIntegral_swap_of_bounded
    (F := fun r beta => V4.paritySigma kappa delta r beta
      * V4.parityV q kappa delta (fun r' _ => w r') r beta ^ 2
      + (w r - V4.paritySigma kappa delta r beta
      * V4.parityV q kappa delta (fun r' _ => w r') r beta) ^ 2
        / Estimates.correctionB q r beta) (hma.add hmb) hbab
  have hdens := V4.parityCompetitor_density_eq hlam hkappa hdelta hmw hbw
  rw [← hswapA, ← hadd, hswapS, hdens]
  rfl

/-! ### `lem:effective-energy` at the parity competitor -/

section Move1

open Manhattan.V4 Manhattan.Operator

/-- **`lem:effective-energy`** (`paper/arxiv/main.tex:951-1033`) at the parity
competitor built from the profile `φ = t/q` on `Γ_δ`, with the column constant
`Cb` of `eq:beta` for `M = 4(δ + |r| + |r'| + |β|)`: the objective of
`lem:variational-bound` is at most `(1 - s ∫φ)²/H₀ + (15/4 + Cb) ∫ q φ²`. -/
theorem move1_objective_paper {Cb : ℝ} (hCb : 0 ≤ Cb) (hB : BetaColumnBound 4 Cb)
    {q : Estimates.Parameters} (hlam : 0 < q.lambda)
    (p : Fin 2 → ℝ) {delta r0 : ℝ}
    (hdelta : 0 < delta) (hlamdelta : q.lambda + 4 * |p 1| ≤ 4 * delta)
    (hr014 : r0 ≤ 1 / 4) (hsqle : Real.sqrt delta ≤ r0)
    (hmud : q.lambda + Estimates.dispersion (p 0) ≤ delta ^ 2) (t : ℝ) :
    ∃ g : Manhattan.WalshL2,
      (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hEnergy q.lambda g
          + (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hlam
              (Manhattan.walshL2 ∅ - Manhattan.concreteFiberA p g)
        ≤ (1 - Real.sin (p 0) * (t * profileMass r0 delta)) ^ 2
              / (q.lambda + Operator.theta p)
            + (15 / 4 + Cb) * (t ^ 2 * profileMass r0 delta) := by
  classical
  have hpi := Real.pi_pos
  have hr01 : r0 < 1 := lt_of_le_of_lt hr014 (by norm_num)
  have hr0pi : r0 < Real.pi := by linarith [Real.pi_gt_three]
  have hsqpos : 0 < Real.sqrt delta := Real.sqrt_pos.mpr hdelta
  have h120 : (0:ℝ) < 4 := by norm_num
  have hmu : 0 < q.lambda + Estimates.dispersion (p 0) :=
    add_pos_of_pos_of_nonneg hlam (Estimates.dispersion_nonneg (p 0))
  have hsinsq : Real.sin (p 0) ^ 2 ≤ 2 * (q.lambda + Estimates.dispersion (p 0)) := by
    have := sin_sq_le_two_dispersion (p 0)
    linarith
  -- the profile
  set phi : ℝ → ℝ := perProfile r0 delta t with hphidef
  set Kp : ℝ := |t| * (Real.sqrt (-Real.log (Real.sqrt delta)) / Real.sqrt delta) with hKpdef
  have hmphi : Measurable phi := measurable_perProfile r0 delta t
  have hbphi : ∀ r, |phi r| ≤ Kp := fun r => perProfile_abs_le hsqpos hsqle hr01 t r
  have hphieven : ∀ r, phi (-r) = phi r := perProfile_even r0 delta t
  have hphiper : Function.Periodic phi (2 * Real.pi) := perProfile_periodic r0 delta t
  have hsupp : ∀ r ∈ Estimates.torus,
      ¬ (Real.sqrt delta ≤ |r| ∧ |r| ≤ r0) → phi r = 0 :=
    fun r hr h => perProfile_supp_torus hr h
  have hint : Integrable (fun r => Energy.effectiveWeight r * phi r ^ 2)
      (volume.restrict Estimates.torus) :=
    integrable_effectiveWeight_perProfile hsqpos hsqle hr01 hr0pi t
  -- the degree-one profile
  set g : ℝ → ℂ := fun x => -Complex.I * ((phi x : ℝ) : ℂ) with hgdef
  have hgmeas : Measurable g := measurable_const.mul (Complex.measurable_ofReal.comp hmphi)
  have hgnorm : ∀ r, ‖g r‖ = |phi r| := by
    intro r
    rw [hgdef]
    simp only
    rw [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have hgb : ∀ r, ‖g r‖ ≤ Kp := fun r => by rw [hgnorm r]; exact hbphi r
  have hgper : Function.Periodic g (2 * Real.pi) := by
    intro x
    show -Complex.I * ((phi (x + 2 * Real.pi) : ℝ) : ℂ) = -Complex.I * ((phi x : ℝ) : ℂ)
    rw [hphiper x]
  have hg : MemLp g 2 (volume.restrict (Set.Ioc (-Real.pi) Real.pi)) :=
    memLp_neg_I_mul hmphi hbphi
  set cco := fourierBasis.repr (rowTorusShift (p 1) (Manhattan.realTorusL2 g hg)) with hccodef
  -- the parity competitor
  set W : ParityProfile := sineProfile phi hmphi Kp hbphi hphieven hphiper with hWdef
  set vp : ParityProfile := parityProfileV hlam h120 hdelta W with hvpdef
  set v : ParityProfile := scaleProfile (Real.sqrt 2) vp with hvdef
  have hK := torusBounded₃_parityKernel h120 hdelta v
  set kc := Manhattan.type112ShiftTwist (p 0) (p 1) (rawType112Coefficients hK) with hkcdef
  have hvcol : ∀ r, Function.Periodic (fun beta => v.toFun r beta) (2 * Real.pi) :=
    scaleProfile_periodic_col (Real.sqrt 2) vp
      (parityProfileV_periodic_col hlam h120 hdelta W (fun _ _ => rfl))
  have hkTwoRow : Manhattan.type112DStarTwoRow p kc = 0 :=
    type112DStarTwoRow_rawShiftTwist hK
      (fun r r' b => parityKernel_neg_col v r r' b) p
  have hcc := inner_empty_residual_shifted p hg kc
  refine ⟨Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal cco
    + Manhattan.type112WalshSynthesis kc, ?_⟩
  rw [objective_eq_sectors hlam p cco kc hkTwoRow hcc]
  -- the two substitution integrals
  have hMass : Estimates.torusIntegral phi = t * profileMass r0 delta :=
    torusIntegral_perProfile r0 delta t
  set E := Estimates.torusIntegral (fun r => Energy.effectiveWeight r * phi r ^ 2) with hEdef
  have hEval : E = t ^ 2 * profileMass r0 delta :=
    torusIntegral_effectiveWeight_perProfile hsqpos hr01 hr0pi t
  set Wr : ℝ → ℝ := fun r => Real.sin r * phi r with hWrdef
  have hmw : Measurable Wr := Real.measurable_sin.mul hmphi
  have hbw : ∀ r, |Wr r| ≤ Kp := by
    intro r
    have h1 := Real.abs_sin_le_one r
    have h2 := hbphi r
    have hKp0 : 0 ≤ Kp := le_trans (abs_nonneg _) (hbphi 0)
    rw [hWrdef]
    simp only
    rw [abs_mul]
    nlinarith [abs_nonneg (Real.sin r), abs_nonneg (phi r)]
  set JJ := Estimates.torusIntegral (fun r => Wr r ^ 2 * parityFibreJ q 4 delta r) with hJJdef
  -- (1) the degree-one energy
  have hE1 : (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hEnergy q.lambda
      (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal cco) ≤ 3 / 4 * E := by
    have heq : (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hEnergy q.lambda
        (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal cco)
        = Estimates.torusIntegral (fun r =>
            (q.lambda + Estimates.dispersion (p 0) + Estimates.dispersion r) * ‖g r‖ ^ 2) :=
      hEnergy_degreeOneRowShift q.lambda p g hg
    rw [heq]
    have hcongr : (fun r => (q.lambda + Estimates.dispersion (p 0)
          + Estimates.dispersion r) * ‖g r‖ ^ 2)
        = fun r => (q.lambda + Estimates.dispersion (p 0)
            + Estimates.dispersion r) * phi r ^ 2 := by
      funext r
      rw [hgnorm r, sq_abs]
    rw [hcongr]
    have hdelta1 : delta ≤ 1 := by
      have h1 : Real.sqrt delta ≤ 1 := by linarith
      have h2 := Real.sq_sqrt hdelta.le
      nlinarith [Real.sqrt_nonneg delta]
    exact degreeOne_cost_le_sharp hmu hdelta hdelta1 hmud hr014 hsupp hint
  -- (2) the two-row sector
  have hE2 : (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hlam
      (Manhattan.type11WalshSynthesis (Manhattan.type11WalshAnalysis
        (walshRaise p (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal cco))))
      ≤ 3 * E := by
    have h := hMinusEnergy_twoRow_le hlam p g hg
    have hcongr : (fun r => ‖g r‖ ^ 2) = fun r => phi r ^ 2 := by
      funext r
      rw [hgnorm r, sq_abs]
    rw [hcongr] at h
    exact h.trans (twoRow_cost_le_sharp (mu := q.lambda + Estimates.dispersion (p 0))
      (s := Real.sin (p 0)) hmu hdelta hmud hsinsq hr014 hsupp hint)
  -- (3) the degree-three cost, `eq:majorant` and `eq:parity-energy`
  have hE3 : sectorHThreeForm q.lambda p (Manhattan.type112WalshSynthesis kc)
      + sectorDFourForm hlam p (Manhattan.type112WalshSynthesis kc) ≤
      Estimates.torusIntegral (fun beta => Estimates.torusIntegral (fun r =>
        paritySigma 4 delta r beta * parityV q 4 delta (fun r' _ => Wr r') r beta ^ 2)) := by
    have hop := sectorForms_rawWalsh_le hlam p hlamdelta hK
      (fun r r' b => parityKernel_swap (kappa := 4) (delta := delta) v.toFun r r' b)
    rw [evenMajorantEnergy_parityKernel h120 hdelta v] at hop
    have hrw : rawWalsh p hK = Manhattan.type112WalshSynthesis kc := rfl
    rw [hrw] at hop
    have hveq : (fun beta => Estimates.torusIntegral (fun r =>
          paritySigma 4 delta r beta * v.toFun r beta ^ 2))
        = fun beta => 2 * Estimates.torusIntegral (fun r =>
          paritySigma 4 delta r beta * parityV q 4 delta (fun r' _ => Wr r') r beta ^ 2) := by
      funext beta
      rw [← Estimates.torusIntegral_smul_left]
      congr 1
      funext r
      exact paritySigma_scaled_sq _ _
    rw [hveq, Estimates.torusIntegral_smul_left] at hop
    linarith
  -- (4) the mixed sector
  have hE4 : (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hlam
      (Manhattan.type12WalshSynthesis
        (Manhattan.type12WalshAnalysis (walshRaise p
            (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal cco))
          - Manhattan.type112DStarMixed p kc)) =
      Estimates.torusIntegral (fun r => Estimates.torusIntegral (fun beta =>
          (Wr r - paritySigma 4 delta r beta
              * parityV q 4 delta (fun r' _ => Wr r') r beta) ^ 2
            / Estimates.correctionB q r beta)) := by
    have hden := hMinusEnergy_v4Mixed_density (q := q) hlam h120 hdelta v hvcol
      hgmeas hgb hgper hg p
    rw [hden]
    congr 1
    funext r
    congr 1
    funext beta
    have hvv : v.toFun r beta
        = Real.sqrt 2 * parityV q 4 delta (fun r' _ => Wr r') r beta := rfl
    rw [norm_v4MixedSymbol_sq 4 delta v phi r beta, hvv, inv_sqrt_two_mul_scaled]
  -- (5) `eq:scalar-energy`
  have hE34 := parityCost_eq (q := q) hlam h120 hdelta hmw hbw
  -- (6) `eq:beta`
  have hE5 : JJ ≤ Cb * E := by
    have h := v4_cost_le_of (q := q) (kappa := 4) (delta := delta) (r0 := r0)
      (C1 := 0) (C3 := 1) hlam h120 hdelta hr014 le_rfl (by norm_num) hCb
      (fun r h1 h2 => hB q delta r hlam hdelta h1 h2) hsupp hint
    have hJJeq : JJ = Estimates.torusIntegral (fun r =>
        Real.sin r ^ 2 * parityFibreJ q 4 delta r * phi r ^ 2) := by
      rw [hJJdef]
      congr 1
      funext r
      rw [hWrdef]
      simp only
      rw [mul_pow]
      ring
    rw [hJJeq]
    have h0 : (0:ℝ) * Estimates.torusIntegral (fun r => (delta + r ^ 2) * phi r ^ 2) = 0 := by
      ring
    rw [h0, zero_add, zero_add] at h
    linarith
  rw [hMass] at hcc ⊢
  rw [hEval] at hE1 hE2 hE5
  rw [hE4]
  linarith

/-- `(π^{5/2} + π)/2 < 11`: the column constant of `eq:beta` at `M = 4(δ + |r| + |r'| + |β|)`. -/
theorem betaColumnConstant_four_le :
    Real.pi * Real.sqrt (Real.pi ^ 3 * 4) / 4 + Real.pi / 2 ≤ 11 := by
  have hpi0 : (0:ℝ) < Real.pi := Real.pi_pos
  have hpi : Real.pi < 3.141593 := Real.pi_lt_d6
  have hsq : Real.pi ^ 2 < 9.8697 := by nlinarith [hpi, hpi0]
  have hcube : Real.pi ^ 3 < 31.008 := by nlinarith [hsq, hpi, hpi0]
  have hs : Real.sqrt (Real.pi ^ 3 * 4) < 11.2 := by
    have h : Real.pi ^ 3 * 4 < 11.2 ^ 2 := by nlinarith [hcube]
    calc Real.sqrt (Real.pi ^ 3 * 4) < Real.sqrt (11.2 ^ 2) :=
          Real.sqrt_lt_sqrt (by positivity) h
      _ = 11.2 := Real.sqrt_sq (by norm_num)
  have hS0 : (0:ℝ) ≤ Real.sqrt (Real.pi ^ 3 * 4) := Real.sqrt_nonneg _
  nlinarith [hs, hpi, hpi0, hS0]

/-- **`lem:effective-energy` with the constant `16`.** -/
theorem move1_objective_sixteen {q : Estimates.Parameters} (hlam : 0 < q.lambda)
    (p : Fin 2 → ℝ) {delta r0 : ℝ}
    (hdelta : 0 < delta) (hlamdelta : q.lambda + 4 * |p 1| ≤ 4 * delta)
    (hr014 : r0 ≤ 1 / 4) (hsqle : Real.sqrt delta ≤ r0)
    (hmud : q.lambda + Estimates.dispersion (p 0) ≤ delta ^ 2) (t : ℝ) :
    ∃ g : Manhattan.WalshL2,
      (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hEnergy q.lambda g
          + (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hlam
              (Manhattan.walshL2 ∅ - Manhattan.concreteFiberA p g)
        ≤ (1 - Real.sin (p 0) * (t * profileMass r0 delta)) ^ 2
              / (q.lambda + Operator.theta p)
            + 16 * (t ^ 2 * profileMass r0 delta) := by
  have hCb : (0:ℝ) ≤ Real.pi * Real.sqrt (Real.pi ^ 3 * 4) / 4 + Real.pi / 2 := by
    have := Real.pi_pos
    positivity
  obtain ⟨g, hg⟩ := move1_objective_paper hCb (betaColumnBound_split (by norm_num)) hlam p
    hdelta hlamdelta hr014 hsqle hmud t
  refine ⟨g, hg.trans ?_⟩
  have hsqle' : Real.sqrt delta ≤ 1 / 4 := le_trans hsqle hr014
  have hr0 : 0 < r0 := lt_of_lt_of_le (Real.sqrt_pos.mpr hdelta) hsqle
  have hm : 0 ≤ t ^ 2 * profileMass r0 delta := by
    rw [← torusIntegral_effectiveWeight_perProfile (Real.sqrt_pos.mpr hdelta)
      (lt_of_le_of_lt hr014 (by norm_num)) (by linarith [Real.pi_gt_three]) t]
    refine Estimates.torusIntegral_nonneg' fun r => ?_
    exact mul_nonneg (Energy.effectiveWeight_nonneg r) (sq_nonneg _)
  have hc := betaColumnConstant_four_le
  nlinarith [hm, hc]

/-- **Move 1 at the frequency `p`**, with `δ = √λ + a(p)`. -/
theorem move1_at_sixteen {lambda : ℝ} (hlambda : 0 < lambda) (hlambda1 : lambda ≤ 1)
    (p : Fin 2 → ℝ) {r0 : ℝ} (hr0 : 0 < r0) (hr014 : r0 ≤ 1 / 4)
    (hp0 : |p 0| ≤ Real.pi)
    (hle : Real.sqrt lambda + Operator.maxFrequency p ≤ r0 ^ 4) (t : ℝ) :
    ∃ g : Manhattan.WalshL2,
      (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hEnergy lambda g
          + (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hlambda
              (Manhattan.walshL2 ∅ - Manhattan.concreteFiberA p g)
        ≤ (1 - Real.sin (p 0)
                * (t * profileMass r0 (Real.sqrt lambda + Operator.maxFrequency p))) ^ 2
              / (lambda + Operator.theta p)
            + 16 * (t ^ 2 * profileMass r0 (Real.sqrt lambda + Operator.maxFrequency p)) := by
  set a := Operator.maxFrequency p with hadef
  have hann : 0 ≤ a := Frequency.maxFrequency_nonneg p
  have hspos : 0 < Real.sqrt lambda := Real.sqrt_pos.mpr hlambda
  set delta := Real.sqrt lambda + a with hdeltadef
  have hdelta : 0 < delta := by positivity
  have hlamsq : lambda ≤ Real.sqrt lambda := self_le_sqrt hlambda hlambda1
  have hp0a : |p 0| ≤ a := le_max_left _ _
  have hp1a : |p 1| ≤ a := le_max_right _ _
  have hsq := Real.sq_sqrt hlambda.le
  have hmud : lambda + Estimates.dispersion (p 0) ≤ delta ^ 2 := by
    have hd := (Estimates.dispersion_quadratic_bounds hp0).2
    have habs : (p 0) ^ 2 ≤ a ^ 2 := by
      have := sq_abs (p 0)
      nlinarith [abs_nonneg (p 0), hp0a]
    have hexp : delta ^ 2 = lambda + 2 * Real.sqrt lambda * a + a ^ 2 := by
      rw [hdeltadef]
      nlinarith [hsq]
    nlinarith [hexp, hd, habs, mul_nonneg hspos.le hann]
  have hlamdelta : lambda + 4 * |p 1| ≤ 4 * delta := by
    rw [hdeltadef]
    nlinarith [hlamsq, hp1a, hspos]
  have hsqle : Real.sqrt delta ≤ r0 :=
    Frequency.sqrt_le_of_le_pow_four hr0 hr014 hle
  exact move1_objective_sixteen (q := v4Parameters lambda) hlambda p hdelta hlamdelta hr014
    hsqle hmud t

/-- **`eq:optimized` with the constant `16`**: `r_λ(p) ≤ 1/(H₀ + s² Z_δ/16)` in the
improvement region, `s = sin p₁` after exchanging rows and columns. -/
theorem move2Supply_sixteen {r0 : ℝ} (hr0 : 0 < r0) (hr014 : r0 ≤ 1 / 4) :
    Frequency.V4Move2Supply r0 16 := by
  have hCpos : (0:ℝ) < 16 := by norm_num
  intro lambda hlambda hlambda1 p hp0 hp1 hle
  have hp0abs : |p 0| ≤ Real.pi := abs_le.2 ⟨hp0.1.le, hp0.2⟩
  have hp1abs : |p 1| ≤ Real.pi := abs_le.2 ⟨hp1.1.le, hp1.2⟩
  have hann : 0 ≤ Operator.maxFrequency p := Frequency.maxFrequency_nonneg p
  have hspos : 0 < Real.sqrt lambda := Real.sqrt_pos.mpr hlambda
  have hr4 : r0 ^ 4 ≤ (1 / 4 : ℝ) ^ 4 := pow_le_pow_left₀ hr0.le hr014 4
  have hasmall : Operator.maxFrequency p ≤ Real.pi / 2 := by
    norm_num at hr4
    nlinarith [Real.pi_gt_three, hspos]
  have hjordan : ∀ x : ℝ, |x| = Operator.maxFrequency p →
      (2 / Real.pi) ^ 2 * Operator.maxFrequency p ^ 2 ≤ x.sin ^ 2 := by
    intro x hx
    have hxle : |x| ≤ Real.pi / 2 := by rw [hx]; exact hasmall
    have hj := Real.mul_abs_le_abs_sin hxle
    have hnn : 0 ≤ 2 / Real.pi * |x| := by positivity
    have hsq := mul_self_le_mul_self hnn hj
    rw [hx] at hsq
    nlinarith [sq_abs (Real.sin x), hsq, sq_abs x]
  rcases le_total (|p 1|) (|p 0|) with hbr | hbr
  · have ha : Operator.maxFrequency p = |p 0| := max_eq_left hbr
    refine ⟨Real.sin (p 0), hjordan (p 0) ha.symm, ?_⟩
    exact v4_move2_at' hCpos hlambda p hr0 hr014 hle
      (fun t => move1_at_sixteen hlambda hlambda1 p hr0 hr014 hp0abs hle t)
  · have ha : Operator.maxFrequency p = |p 1| := max_eq_right hbr
    refine ⟨Real.sin (p 1), hjordan (p 1) ha.symm, ?_⟩
    refine v4_move2_at' hCpos hlambda p hr0 hr014 hle ?_
    intro t
    have hswap : Operator.maxFrequency (axisSwapFrequency p) = Operator.maxFrequency p :=
      axisSwap_maxFrequency p
    have hth : Operator.theta (axisSwapFrequency p) = Operator.theta p := axisSwap_theta p
    have hle' : Real.sqrt lambda + Operator.maxFrequency (axisSwapFrequency p) ≤ r0 ^ 4 := by
      rw [hswap]; exact hle
    have h0' : |axisSwapFrequency p 0| ≤ Real.pi := by
      rw [axisSwapFrequency_zero]; exact hp1abs
    have hm := move1_at_sixteen hlambda hlambda1 (axisSwapFrequency p) hr0 hr014 h0' hle' t
    rw [hswap, hth, axisSwapFrequency_zero] at hm
    exact objective_of_axisSwap hlambda p hm

end Move1

end

end Manhattan.Paper
