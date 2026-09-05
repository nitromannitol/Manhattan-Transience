import Manhattan.Glue.FinalDischarge
import Manhattan.Glue.SummandsMixed
import Manhattan.Glue.ConcreteRaisingFourier
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Summand 4 of (22): the degree-four raising sector

Summand 4 of the four-sector form (22) is `‖D₃k_p‖²_{-1}`, read off
as the degree-four Walsh sector of the unnormalized residual
(`Manhattan.Glue.SummandFourBound`). The paper bounds it in the second half
of Lemma 5.2 (`manuscript.tex:1196-1205`, proof at
`manuscript.tex:1257-1272`): drop the projections by (46), bound the square of
the raising sum of (45) by the number of its terms times the sum of squares,
and integrate each term over the frequency of the line sign just added, where
the line integral (22) turns `(λ+θ(P))⁻¹` into `(λ+d(P_i))^{-1/2}`.

This file supplies three of the ingredients of that argument.

* The **structural reduction**: the degree-four Walsh sector of `A_p k` is the
  raising half alone, its Walsh coefficients are the adjoint lowering
  pairings, and it lies in the degree-four chaos
  (`walshSectorComponent_four_concreteFiberA`, `inner_walshL2_sectorFour`,
  `walshSectorComponent_card_mem_walshDegree`).
* The **`H⁻¹` transport in a fixed degree**: for a homogeneous vector the dual
  energy is the explicit weighted line-frequency integral of (20)
  (`hMinusEnergy_homogeneousWalshSynthesis`,
  `sectorDFourForm_eq_integral`). This is the `H⁻¹` companion of
  `Manhattan.Glue.re_inner_coeffH_eq_integral`, which the formalization used for the
  `H₃` half.
* The **momentum comparison**: `Manhattan.correctionType112Coefficients` takes
  the Fourier coefficients of the manuscript's `k̃` in the shifted variables
  `(r,r',β)` of `manuscript.tex:812-814` without the compensating phase, so
  the objective's total frequency at the momentum `p` differs from the
  manuscript's by `(p₁, p₂+p₂)`. Wherever `k̃` is nonzero, the support
  intervals of `manuscript.tex:1040-1063` separate `α` from the origin by
  `4K(a+√λ+|β|)`, which dominates that shift with room to spare; the raising
  density at the momentum `p` is then at most eight times the raising density
  of `rawCubicRaisingEnergy` (`sineSqDivSqrt_shift_le`).

Paper: `manuscript.tex:1196-1205`, `manuscript.tex:1257-1272`,
`manuscript.tex:812-814`, `manuscript.tex:1040-1063`.
-/

noncomputable section

open MeasureTheory UnitAddTorus Set
open ComplexConjugate InnerProductSpace RCLike

namespace Manhattan.Glue

/-! ### Walsh-coefficient extensionality

The vector form of the principle, kept private here so that the file does not
depend on which of the two ancestor modules exports it. -/

private theorem walshVector_ext {x y : WalshL2}
    (h : ∀ S : Finset LineIndex,
      inner ℂ (Manhattan.walshL2 S) x = inner ℂ (Manhattan.walshL2 S) y) :
    x = y := by
  apply Manhattan.walshBasis.repr.injective
  apply lp.ext
  funext S
  rw [Manhattan.walshBasis.repr_apply_apply, Manhattan.walshBasis.repr_apply_apply,
    Manhattan.walshBasis_apply, h]

/-! ### The degree-four sector of `A_p k` -/

/-- The degree-four Walsh sector of a difference of a degree-four and a
degree-two vector is the degree-four term. This is the degree bookkeeping of
`A = D - D*` (`manuscript.tex:735-737`) in the sector of (22). -/
theorem walshSectorComponent_four_sub {a b : WalshL2}
    (ha : a ∈ Manhattan.walshDegree 4) (hb : b ∈ Manhattan.walshDegree 2) :
    walshSectorComponent (fun S => S.card = 4) (a - b) = a := by
  refine walshVector_ext fun U => ?_
  rw [inner_walshL2_walshSectorComponent]
  by_cases h : U.card = 4
  · rw [if_pos h, inner_sub_right,
      inner_walshL2_eq_zero_of_mem_walshDegree hb (by omega), sub_zero]
  · rw [if_neg h, inner_walshL2_eq_zero_of_mem_walshDegree ha h]

/-- Every Walsh sector cut out by a cardinality condition lands in the
corresponding closed Walsh chaos. -/
theorem walshSectorComponent_card_mem_walshDegree (n : ℕ) (x : WalshL2) :
    walshSectorComponent (fun S => S.card = n) x ∈ Manhattan.walshDegree n := by
  classical
  set P : Finset LineIndex → Prop := fun S => S.card = n with hP
  have hs : HasSum (fun T : {S : Finset LineIndex // P S} =>
      Manhattan.walshSectorAnalysis P x T • Manhattan.walshL2 T.1)
      (walshSectorSynthesis P (Manhattan.walshSectorAnalysis P x)) := by
    simpa only [walshSectorSynthesis, walshSectorFamily,
      LinearIsometry.toSpanSingleton_apply] using
      (orthonormal_walshSectorFamily P).orthogonalFamily.hasSum_linearIsometry
        (Manhattan.walshSectorAnalysis P x)
  refine (Submodule.isClosed_topologicalClosure _).mem_of_tendsto hs
    (Filter.Eventually.of_forall fun s => Submodule.sum_mem _ fun T _ => ?_)
  refine Submodule.smul_mem _ _ ?_
  have := Manhattan.walshL2_mem_degree T.1
  rwa [T.2] at this

/-- **Equation (45) in adjoint form.** On a degree-four index the Walsh
coefficient of the degree-four sector of `A_p k` is the pairing of `k` with
the finite lowering coefficient of that index; the raising half of `A_p`
lands in degree five and drops out. -/
theorem inner_walshL2_sectorFour (p : Fin 2 → ℝ) {k : WalshL2}
    (hk : k ∈ Manhattan.walshDegree 3) {T : Finset LineIndex} (hT : T.card = 4) :
    inner ℂ (Manhattan.walshL2 T)
        (walshSectorComponent (fun S => S.card = 4) (Manhattan.concreteFiberA p k)) =
      inner ℂ (Manhattan.walshSynthesis
        (Manhattan.fiberDStarLoweringSpatialCoefficient p T)) k := by
  rw [inner_walshL2_walshSectorComponent, if_pos hT,
    ← (Manhattan.concreteFiberA p).adjoint_inner_left,
    Manhattan.concreteFiberA_skewAdjoint, ContinuousLinearMap.neg_apply,
    Manhattan.concreteFiberA_walshL2_eq_D_sub_DStar, inner_neg_left,
    inner_sub_left,
    inner_walshSynthesis_eq_zero_of_mem_walshDegree
      (Manhattan.isWalshDegree_fiberDRaisingSpatialCoefficient p T hT) hk
      (by omega)]
  ring

/-- The degree-four sector of `A_p k` has a degree-four coefficient
sequence. -/
theorem exists_sectorFour_coefficient (p : Fin 2 → ℝ) (k : WalshL2) :
    ∃ c : DegreeCoefficient 4, homogeneousWalshSynthesis 4 c =
      walshSectorComponent (fun S => S.card = 4) (Manhattan.concreteFiberA p k) := by
  have h := walshSectorComponent_card_mem_walshDegree 4 (Manhattan.concreteFiberA p k)
  rw [← SetLike.mem_coe, walshDegree_eq_range] at h
  exact h

/-! ### The `H⁻¹` energy in a fixed Walsh degree -/

/-- **The `H⁻¹` transport in degree `n`.** For a homogeneous vector the dual
energy of (12) is the integral of `(λ+θ(P))⁻¹` against the squared modulus of
the line-frequency coefficient of equation (20). This is the `H⁻¹` companion
of `re_inner_coeffH_eq_integral`. -/
theorem hMinusEnergy_homogeneousWalshSynthesis (n : ℕ) {lam : ℝ} (hlam : 0 < lam)
    (p : Fin 2 → ℝ) (c : DegreeCoefficient n) :
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hlam
        (homogeneousWalshSynthesis n c) =
      ∑' σ : Fin n → Axis,
        ∫ t, (symbolWeight n lam p σ t)⁻¹ *
          ‖((lineIndexFourier n c) σ) t‖ ^ 2 ∂(LineTorusMeasure n) := by
  obtain ⟨d, hd⟩ := (coeffH_bijective n hlam p).2 c
  have hinv :
      ((Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hEquiv hlam).symm
          (homogeneousWalshSynthesis n c) = homogeneousWalshSynthesis n d := by
    rw [ContinuousLinearEquiv.symm_apply_eq]
    show homogeneousWalshSynthesis n c =
      (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).H lam
        (homogeneousWalshSynthesis n d)
    rw [fiberH_homogeneousWalshSynthesis, hd]
  rw [Manhattan.Operator.DissipativeSkewPair.hMinusEnergy, hinv,
    (homogeneousWalshSynthesis n).inner_map_map,
    ← re_inner_coeffH_inv_eq_integral n hlam p c d hd,
    ← inner_conj_symm (𝕜 := ℂ) d c, RCLike.conj_re]

/-- **Summand 4 of (22) as a weighted line-frequency integral.** -/
theorem sectorDFourForm_eq_integral {lambda : ℝ} (hlambda : 0 < lambda)
    (p : Fin 2 → ℝ) (k : WalshL2) (c : DegreeCoefficient 4)
    (hc : homogeneousWalshSynthesis 4 c =
      walshSectorComponent (fun S => S.card = 4) (Manhattan.concreteFiberA p k)) :
    sectorDFourForm hlambda p k =
      ∑' σ : Fin 4 → Axis,
        ∫ t, (symbolWeight 4 lambda p σ t)⁻¹ *
          ‖((lineIndexFourier 4 c) σ) t‖ ^ 2 ∂(LineTorusMeasure 4) := by
  rw [sectorDFourForm, ← hc, hMinusEnergy_homogeneousWalshSynthesis]

/-! ### The momentum comparison for the raising density -/

/-- The `α`-interval of `manuscript.tex:1040-1063` is separated from the
origin by `4K(a+√λ+|β|)`. This sharpens `correctionInterval_bounds`, which
records only the separation `4Ka`. -/
theorem correctionInterval_bounds_strong {q : Manhattan.Estimates.Parameters}
    (hK : 0 ≤ q.K) {a s beta alpha : ℝ} (ha : 0 ≤ a)
    (h : alpha ∈ Manhattan.Estimates.correctionInterval q a s beta) :
    alpha ≤ -(4 * q.K * (a + Real.sqrt q.lambda + |beta|)) ∧ -q.rho ≤ alpha := by
  classical
  unfold Manhattan.Estimates.correctionInterval at h
  by_cases hcond : s ∈ q.supportInterval a ∧
      s + q.delta a + |beta| ≤ q.rho / (8 * q.K)
  · rw [if_pos hcond] at h
    obtain ⟨hlow, hhigh⟩ := h
    have hdeltaNonneg : 0 ≤ q.delta a := by
      rw [Manhattan.Estimates.Parameters.delta]
      have := Real.sqrt_nonneg q.lambda
      linarith
    have hs : q.K * q.delta a ≤ s := hcond.1.1
    have hsNonneg : 0 ≤ s := le_trans (by positivity) hs
    refine ⟨hhigh.trans ?_, hlow⟩
    have hdelta : q.delta a = Real.sqrt q.lambda + a := rfl
    have hmono : a + Real.sqrt q.lambda + |beta| ≤ s + q.delta a + |beta| := by
      rw [hdelta]; linarith
    have hKpos : (0 : ℝ) ≤ 4 * q.K := by linarith
    have := mul_le_mul_of_nonneg_left hmono hKpos
    linarith
  · rw [if_neg hcond] at h
    exact absurd h (Set.notMem_empty _)

private theorem pi_sq_le_ten : Real.pi ^ 2 ≤ 10 := by
  nlinarith [Real.pi_lt_d4, Real.pi_pos]

set_option maxHeartbeats 1000000 in
/-- **The scalar momentum comparison.** When the frequency `α` is separated
from the origin by `80(a+√λ+|β|)` and stays in `[-π/20,0]`, shifting the two
total-frequency coordinates by amounts of size at most `a` and `2a` costs at
most a factor `8/√2` in the raising density `sin²(P)/√(λ+d(P))` of
`manuscript.tex:1265-1270`. -/
theorem sineSqDivSqrt_shift_le_scalar {lam a c0 c1 alpha beta : ℝ}
    (hlam : 0 < lam) (ha : 0 ≤ a) (hc0 : |c0| ≤ a) (hc1 : |c1| ≤ 2 * a)
    (hsep : alpha ≤ -(80 * (a + Real.sqrt lam + |beta|)))
    (hlow : -(Real.pi / 20) ≤ alpha) :
    Real.sqrt 2 *
        (Real.sin (beta + c0) ^ 2 /
            Real.sqrt (lam + Manhattan.Estimates.dispersion (beta + c0)) +
          Real.sin (alpha + c1) ^ 2 /
            Real.sqrt (lam + Manhattan.Estimates.dispersion (alpha + c1))) ≤
      8 * (Real.sin beta ^ 2 /
            Real.sqrt (lam + Manhattan.Estimates.dispersion beta) +
          Real.sin alpha ^ 2 /
            Real.sqrt (lam + Manhattan.Estimates.dispersion alpha)) := by
  have hsqrtpos : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hsqrtnn : (0 : ℝ) ≤ Real.sqrt lam := Real.sqrt_nonneg _
  have hbetann : (0 : ℝ) ≤ |beta| := abs_nonneg _
  have hpid4 : Real.pi < 3.1416 := Real.pi_lt_d4
  have hpipos : 0 < Real.pi := Real.pi_pos
  set u : ℝ := -alpha with hu
  have hualpha : alpha = -u := by rw [hu]; ring
  have hupos : 0 < u := by rw [hu]; linarith
  have hau : a ≤ u / 80 := by rw [hu]; linarith
  have hsu : Real.sqrt lam ≤ u / 80 := by rw [hu]; linarith
  have hbu : |beta| ≤ u / 80 := by rw [hu]; linarith
  have hurho : u ≤ Real.pi / 20 := by rw [hu]; linarith
  have husmall : u ≤ 0.1571 := by linarith
  have hlamu : lam ≤ u ^ 2 / 6400 := by
    have h := Real.sq_sqrt hlam.le
    nlinarith [hsu, hsqrtnn, hupos]
  have hsqrt2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hsqrt2nn : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hupper : ∀ y : ℝ, Real.sin y ^ 2 /
      Real.sqrt (lam + Manhattan.Estimates.dispersion y) ≤ Real.sqrt 2 * |y| := by
    intro y
    have h1 := Manhattan.Estimates.sine_sq_div_sqrt_le lam y hlam.le
    have h2 : |Real.sin (y / 2)| ≤ |y| / 2 := by
      have h := Real.abs_sin_le_abs (x := y / 2)
      rwa [abs_div, abs_two] at h
    have h3 : 2 * Real.sqrt 2 * |Real.sin (y / 2)| ≤ 2 * Real.sqrt 2 * (|y| / 2) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    calc Real.sin y ^ 2 / Real.sqrt (lam + Manhattan.Estimates.dispersion y)
        ≤ 2 * Real.sqrt 2 * |Real.sin (y / 2)| := h1
      _ ≤ 2 * Real.sqrt 2 * (|y| / 2) := h3
      _ = Real.sqrt 2 * |y| := by ring
  have habsalpha : |alpha| = u := by
    rw [hualpha, abs_neg, abs_of_nonneg hupos.le]
  have hshift0 : |beta + c0| ≤ u / 40 := by
    have h := abs_add_le beta c0
    linarith
  have hshift1 : |alpha + c1| ≤ u * (1 + 1 / 40) := by
    have h1 := abs_add_le alpha c1
    linarith
  have hT0 : Real.sin (beta + c0) ^ 2 /
      Real.sqrt (lam + Manhattan.Estimates.dispersion (beta + c0)) ≤
        Real.sqrt 2 * (u / 40) :=
    (hupper (beta + c0)).trans (mul_le_mul_of_nonneg_left hshift0 hsqrt2nn)
  have hT1 : Real.sin (alpha + c1) ^ 2 /
      Real.sqrt (lam + Manhattan.Estimates.dispersion (alpha + c1)) ≤
        Real.sqrt 2 * (u * (1 + 1 / 40)) :=
    (hupper (alpha + c1)).trans (mul_le_mul_of_nonneg_left hshift1 hsqrt2nn)
  have hexp : Real.sqrt 2 *
      (Real.sqrt 2 * (u / 40) + Real.sqrt 2 * (u * (1 + 1 / 40))) = 2.1 * u := by
    linear_combination (u / 40 + u * (1 + 1 / 40)) * hsqrt2
  have hLHS : Real.sqrt 2 *
      (Real.sin (beta + c0) ^ 2 /
          Real.sqrt (lam + Manhattan.Estimates.dispersion (beta + c0)) +
        Real.sin (alpha + c1) ^ 2 /
          Real.sqrt (lam + Manhattan.Estimates.dispersion (alpha + c1))) ≤
      2.1 * u := by
    refine le_trans (mul_le_mul_of_nonneg_left (add_le_add hT0 hT1) hsqrt2nn) ?_
    exact le_of_eq hexp
  have habspi : |alpha| ≤ Real.pi := by rw [habsalpha]; linarith
  obtain ⟨hdlo, hdhi⟩ := Manhattan.Estimates.dispersion_quadratic_bounds habspi
  set d : ℝ := Manhattan.Estimates.dispersion alpha with hd
  have halphasq : alpha ^ 2 = u ^ 2 := by rw [hualpha]; ring
  have hpisq : Real.pi ^ 2 ≤ 10 := pi_sq_le_ten
  have hp2 : (0 : ℝ) < Real.pi ^ 2 := by positivity
  rw [halphasq] at hdlo hdhi
  have hdlo' : u ^ 2 / 5 ≤ d := by
    have hstep : u ^ 2 / 5 ≤ 2 * u ^ 2 / Real.pi ^ 2 := by
      rw [le_div_iff₀ hp2]
      nlinarith [hupos, hpisq]
    linarith
  have husq : u ^ 2 ≤ 0.025 := by nlinarith [hupos, husmall]
  have hdsmall : d ≤ 0.02 := by linarith
  have hsinid : Real.sin alpha ^ 2 = d * (2 - d) := by
    have h := Real.sin_sq_add_cos_sq alpha
    rw [hd]
    unfold Manhattan.Estimates.dispersion
    linear_combination h
  have hdnn : (0 : ℝ) ≤ d := by
    rw [hd]; exact Manhattan.Estimates.dispersion_nonneg alpha
  have hdenle : Real.sqrt (lam + d) ≤ 0.72 * u := by
    have hsq : (0.72 * u) ^ 2 = 0.5184 * u ^ 2 := by ring
    have hle : lam + d ≤ (0.72 * u) ^ 2 := by
      rw [hsq]; linarith [sq_nonneg u]
    calc Real.sqrt (lam + d) ≤ Real.sqrt ((0.72 * u) ^ 2) := Real.sqrt_le_sqrt hle
      _ = 0.72 * u := Real.sqrt_sq (by positivity)
  have hdenpos : 0 < Real.sqrt (lam + d) := Real.sqrt_pos.mpr (by linarith)
  have hmul : (1 / 2 : ℝ) * u * Real.sqrt (lam + d) ≤ (1 / 2 : ℝ) * u * (0.72 * u) :=
    mul_le_mul_of_nonneg_left hdenle (by positivity)
  have hdd : 1.98 * d ≤ d * (2 - d) := by
    have h : 0 ≤ d * (0.02 - d) := mul_nonneg hdnn (by linarith)
    linarith
  have hkey : (1 / 2 : ℝ) * u ≤ Real.sin alpha ^ 2 / Real.sqrt (lam + d) := by
    rw [le_div_iff₀ hdenpos, hsinid]
    linarith
  have hbetann2 : (0 : ℝ) ≤ Real.sin beta ^ 2 /
      Real.sqrt (lam + Manhattan.Estimates.dispersion beta) :=
    div_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)
  linarith

/-- **The momentum comparison at the concrete competitor.** Wherever the
manuscript's `k̃` is nonzero, the raising density at the objective's momentum
`p` is at most eight times the raising density at the manuscript's frozen
frequencies, which is the integrand of `rawCubicRaisingEnergy`. -/
theorem sineSqDivSqrt_shift_le {q : Manhattan.Estimates.Parameters}
    (hlambda : 0 < q.lambda) (hK : q.K = 20) (hrho : q.rho = Real.pi / 20)
    (p : Fin 2 → ℝ) (horder : |p 1| ≤ |p 0|)
    {x : UnitAddTorus (Fin 3)}
    (hnz : Manhattan.rawCorrectionFunction 40 q |p 0| (p 1) x ≠ 0) :
    Real.sqrt 2 *
        (Real.sin (rawCorrectionTotalFrequency (p 1) x 0 + p 0) ^ 2 /
            Real.sqrt (q.lambda + Manhattan.Estimates.dispersion
              (rawCorrectionTotalFrequency (p 1) x 0 + p 0)) +
          Real.sin (rawCorrectionTotalFrequency (p 1) x 1 + (p 1 + p 1)) ^ 2 /
            Real.sqrt (q.lambda + Manhattan.Estimates.dispersion
              (rawCorrectionTotalFrequency (p 1) x 1 + (p 1 + p 1)))) ≤
      8 * (Real.sin (rawCorrectionTotalFrequency (p 1) x 0) ^ 2 /
            Real.sqrt (q.lambda + Manhattan.Estimates.dispersion
              (rawCorrectionTotalFrequency (p 1) x 0)) +
          Real.sin (rawCorrectionTotalFrequency (p 1) x 1) ^ 2 /
            Real.sqrt (q.lambda + Manhattan.Estimates.dispersion
              (rawCorrectionTotalFrequency (p 1) x 1))) := by
  classical
  have hbeta : rawCorrectionTotalFrequency (p 1) x 0 =
      Manhattan.unitTorusAngle (x 2) := by
    simp [rawCorrectionTotalFrequency, Manhattan.Estimates.mixedTotalFrequency]
  have halpha : rawCorrectionTotalFrequency (p 1) x 1 =
      Manhattan.unitTorusAngle (x 0) + Manhattan.unitTorusAngle (x 1) - p 1 := by
    simp [rawCorrectionTotalFrequency, Manhattan.Estimates.mixedTotalFrequency]
  have hmem := mem_correctionInterval_of_ne_zero (kappa := 40) (q := q) |p 0| (p 1)
    (Manhattan.unitTorusAngle (x 0)) (Manhattan.unitTorusAngle (x 1))
    (Manhattan.unitTorusAngle (x 2)) hnz
  have hKnn : (0 : ℝ) ≤ q.K := by rw [hK]; norm_num
  have ha : (0 : ℝ) ≤ |p 0| := abs_nonneg _
  have hbounds :
      (Manhattan.unitTorusAngle (x 0) + Manhattan.unitTorusAngle (x 1) - p 1)
          ≤ -(4 * q.K * (|p 0| + Real.sqrt q.lambda +
            |Manhattan.unitTorusAngle (x 2)|)) ∧
      -q.rho ≤ Manhattan.unitTorusAngle (x 0) +
        Manhattan.unitTorusAngle (x 1) - p 1 := by
    rcases hmem with hm | hm
    · exact correctionInterval_bounds_strong hKnn ha hm
    · exact correctionInterval_bounds_strong hKnn ha hm
  obtain ⟨hsep, hlow⟩ := hbounds
  rw [hK] at hsep
  rw [hrho] at hlow
  rw [hbeta, halpha]
  refine sineSqDivSqrt_shift_le_scalar hlambda ha le_rfl ?_ (by linarith) hlow
  have h2 := abs_add_le (p 1) (p 1)
  linarith

/-! ### The degree-four sector is the raising half, direction by direction -/

/-- With `A = D - D*` the degree-four sector of `A_p k` is the raising half
`D k` itself. -/
theorem walshSectorComponent_four_walshRaise (p : Fin 2 → ℝ) {k : WalshL2}
    (hk : k ∈ Manhattan.walshDegree 3) :
    walshSectorComponent (fun S => S.card = 4) (Manhattan.concreteFiberA p k) =
      walshRaise p k := by
  have h : Manhattan.concreteFiberA p k = walshRaise p k - walshLower p k := by
    rw [concreteFiberA_eq_walshRaise_sub_walshLower]; rfl
  rw [h]
  exact walshSectorComponent_four_sub (walshRaise_mem_walshDegree p hk)
    (by simpa using walshLower_mem_walshDegree p hk)

/-- One direction of the raising operator moves the degree-three chaos into
degree four exactly: every Walsh coefficient at an index of a different
cardinality vanishes. -/
theorem inner_walshL2_walshRaiseDir_eq_zero (p : Fin 2 → ℝ) (i : Fin 2)
    {k : WalshL2} (hk : k ∈ Manhattan.walshDegree 3) {T : Finset LineIndex}
    (hT : T.card ≠ 4) :
    inner ℂ (Manhattan.walshL2 T) (walshRaiseDir p i k) = 0 := by
  classical
  rw [inner_walshL2_walshRaiseDir]
  by_cases h : originLine i ∈ T
  · rw [if_pos h]
    have hcard : (T.erase (originLine i)).card ≠ 3 := by
      rw [Finset.card_erase_of_mem h]
      omega
    rw [inner_walshL2_eq_zero_of_mem_walshDegree hk
        (by rwa [Manhattan.card_translateWalshIndex]),
      inner_walshL2_eq_zero_of_mem_walshDegree hk
        (by rwa [Manhattan.card_translateWalshIndex])]
    ring
  · rw [if_neg h]

/-- Consequently each direction of `D` maps the degree-three chaos into the
degree-four chaos. -/
theorem walshRaiseDir_mem_walshDegree (p : Fin 2 → ℝ) (i : Fin 2)
    {k : WalshL2} (hk : k ∈ Manhattan.walshDegree 3) :
    walshRaiseDir p i k ∈ Manhattan.walshDegree 4 := by
  have heq : walshRaiseDir p i k =
      walshSectorComponent (fun S => S.card = 4) (walshRaiseDir p i k) := by
    refine walshVector_ext fun U => ?_
    rw [inner_walshL2_walshSectorComponent]
    by_cases h : U.card = 4
    · rw [if_pos h]
    · rw [if_neg h, inner_walshL2_walshRaiseDir_eq_zero p i hk h]
  rw [heq]
  exact walshSectorComponent_card_mem_walshDegree 4 _

/-- Each direction of the raised vector has a degree-four coefficient
sequence. -/
theorem exists_walshRaiseDir_coefficient (p : Fin 2 → ℝ) (i : Fin 2)
    {k : WalshL2} (hk : k ∈ Manhattan.walshDegree 3) :
    ∃ c : DegreeCoefficient 4,
      homogeneousWalshSynthesis 4 c = walshRaiseDir p i k := by
  have h := walshRaiseDir_mem_walshDegree p i hk
  rw [← SetLike.mem_coe, walshDegree_eq_range] at h
  exact h

/-- **Splitting the two raising directions.** The parallelogram bound for the
dual energy costs the factor two of the two-term Cauchy--Schwarz of
`manuscript.tex:1257-1272` and leaves no cross term. -/
theorem sectorDFourForm_le_dirs {lambda : ℝ} (hlambda : 0 < lambda)
    (p : Fin 2 → ℝ) {k : WalshL2} (hk : k ∈ Manhattan.walshDegree 3) :
    sectorDFourForm hlambda p k ≤
      2 * (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy
            hlambda (walshRaiseDir p 0 k) +
        2 * (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy
            hlambda (walshRaiseDir p 1 k) := by
  rw [sectorDFourForm, walshSectorComponent_four_walshRaise p hk,
    show walshRaise p k = walshRaiseDir p 0 k + walshRaiseDir p 1 k by
      rw [walshRaise, ContinuousLinearMap.sum_apply, Fin.sum_univ_two]]
  exact hMinusEnergy_add_le _ hlambda _ _

/-- **Summand 4 as two weighted line-frequency integrals in degree four.**
This is the exact remaining analytic content of the second half of Lemma 5.2:
each of the two directions contributes the `H⁻¹` integral of its own
degree-four coefficient. -/
theorem sectorDFourForm_le_dir_integrals {lambda : ℝ} (hlambda : 0 < lambda)
    (p : Fin 2 → ℝ) {k : WalshL2} (hk : k ∈ Manhattan.walshDegree 3)
    (c : Fin 2 → DegreeCoefficient 4)
    (hc : ∀ i, homogeneousWalshSynthesis 4 (c i) = walshRaiseDir p i k) :
    sectorDFourForm hlambda p k ≤
      2 * (∑' σ : Fin 4 → Axis,
          ∫ t, (symbolWeight 4 lambda p σ t)⁻¹ *
            ‖((lineIndexFourier 4 (c 0)) σ) t‖ ^ 2 ∂(LineTorusMeasure 4)) +
        2 * (∑' σ : Fin 4 → Axis,
          ∫ t, (symbolWeight 4 lambda p σ t)⁻¹ *
            ‖((lineIndexFourier 4 (c 1)) σ) t‖ ^ 2 ∂(LineTorusMeasure 4)) := by
  have h0 := hMinusEnergy_homogeneousWalshSynthesis 4 hlambda p (c 0)
  have h1 := hMinusEnergy_homogeneousWalshSynthesis 4 hlambda p (c 1)
  rw [hc 0] at h0
  rw [hc 1] at h1
  rw [← h0, ← h1]
  exact sectorDFourForm_le_dirs hlambda p hk

/-! ### The reduction of `SummandFourBound` -/

/-- **The reduction of summand 4 of (22).** `SummandFourBound C` is exactly
the bound on `sectorDFourForm` at the projected correction `k_p`; the passage
through the unnormalized residual is `sector_four_residual_eq`. -/
theorem summandFourBound_of_sectorDFour {C : ℝ}
    (h : ∀ {lambda : ℝ}, ∀ hlambda : 0 < lambda, lambda ≤ 1 → ∀ p : Fin 2 → ℝ,
      p 0 ∈ Manhattan.Estimates.torus → p 1 ∈ Manhattan.Estimates.torus →
      |p 1| ≤ |p 0| → 0 < |p 0| →
      (⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩ :
          Manhattan.Estimates.Parameters).logThreshold <
        (⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩ :
          Manhattan.Estimates.Parameters).scaleLog |p 0| →
      sectorDFourForm hlambda p
          (Manhattan.shiftedCorrectionWalsh (kappa := 40) (by norm_num)
            (q := ⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩)
            hlambda |p 0| (p 0) (p 1)) ≤
        C * Real.sqrt ((⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩ :
          Manhattan.Estimates.Parameters).scaleLog |p 0|)) :
    SummandFourBound C := by
  intro lambda hlambda hlambdaOne p hp₀ hp₁ horder hpositive
  let q : Manhattan.Estimates.Parameters :=
    ⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩
  change q.logThreshold < q.scaleLog |p 0| → _
  intro hlog hcert hnormalization
  refine le_trans (le_of_eq (sector_four_residual_eq hlambda p
      (correctedLowDegreeData hlambda p hcert hnormalization))) ?_
  refine le_trans ?_ (h hlambda hlambdaOne p hp₀ hp₁ horder hpositive hlog)
  rw [correctedMixedVector_eq,
    correctedLowDegreeData_mixed_eq hlambda p hcert hnormalization]
  exact sectorDFourForm_ofReal_sign_smul_le hlambda p _ _

end Manhattan.Glue
