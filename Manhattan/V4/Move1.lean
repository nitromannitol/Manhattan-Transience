import Manhattan.V4.Move1Cost
import Manhattan.V4.Sectors

/-!
# Version 4, Move 1: the effective-energy inequality at the parity competitor

This file assembles the four sector identifications into the Move 1 inequality
of the Version 4 argument, in the exact shape
`Manhattan.V4.Frequency.move2_bound` consumes:

  `r_λ(p) ≤ (1 - s ∫ φ dm)²/h₀ + C ∫ q φ² dm`, `h₀ = λ + θ(p)`, `s = sin p₁`.

The competitor is the pair `(f_p, k_p)` with
`f_p = axisDegreeOneSynthesis horizontal (fourierBasis.repr (rowTorusShift (p 1)
(realTorusL2 (-iφ))))` and `k_p = Π₃ K` at the parity kernel of the formalization, built
from the profile `v = √2 w/(B+σ)`, `w(r) = sin(r) φ(r)`.

The four pieces are

* the degree-zero residual, with coefficient **one** on `h₀`
  (`Manhattan.V4.hMinusEnergy_empty_add` of `Manhattan/V4/Sectors.lean`);
* the degree-one energy `2 ⟨f_p, H f_p⟩ ≤ 12 ∫ q φ²` and the two-row sector
  `4 ‖(D₁f)₁₁‖²₋₁ ≤ 48 ∫ q φ²`, together estimate (4) with `C₁ = 60`;
* the degree-three cost `2(‖k‖₊² + ‖D₃k‖₋²) ≤ 36 ∫ w² J₃` and the degree-two
  mixed residual `4 ‖(D₁f - D₂*k)₁₂‖²₋₁ ≤ 4 ∫ w² J₃`, together `40 ∫ w² J₃`;
* ingredient (6), `40 ∫ w² J₃ ≤ 40(π² + π³κ/2) ∫ q φ²` at `κ = 120`.

The composed constant is therefore `C = 60 + 40(π² + 60π³)`.

The statement is an existential over the competitor rather than a bound on
`resolventQuadratic` directly, so that it can be transported through the axis
swap `Manhattan.Glue.axisSwap_competitorObjective`.
-/

noncomputable section
open MeasureTheory Set

namespace Manhattan.V4

open Manhattan.Glue Manhattan.Operator


/-- The purely imaginary degree-one profile of a bounded measurable real profile
is square integrable on the torus. -/
theorem memLp_neg_I_mul {phi : ℝ → ℝ} (hm : Measurable phi) {K : ℝ}
    (hb : ∀ r, |phi r| ≤ K) :
    MemLp (fun x => -Complex.I * ((phi x : ℝ) : ℂ)) 2
      (volume.restrict (Set.Ioc (-Real.pi) Real.pi)) := by
  have hmeas : Measurable fun x => -Complex.I * ((phi x : ℝ) : ℂ) :=
    measurable_const.mul (Complex.measurable_ofReal.comp hm)
  have h : MemLp (fun x => -Complex.I * ((phi x : ℝ) : ℂ)) 2
      (volume.restrict Estimates.torus) := by
    refine MemLp.of_bound hmeas.aestronglyMeasurable K ?_
    filter_upwards with x
    rw [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    exact hb x
  exact h

theorem norm_neg_I_mul_sq (phi : ℝ → ℝ) (r : ℝ) :
    ‖(-Complex.I * ((phi r : ℝ) : ℂ))‖ ^ 2 = phi r ^ 2 := by
  rw [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    sq_abs]

/-- **The Version 4 degree-zero coefficient at the shifted row synthesis.** The
row shift of `(shift)` does not move the degree-zero Fourier coefficient
(`Manhattan.Glue.fourierBasis_repr_rowTorusShift_zero`), so the numerator of
Move 1 is unchanged: it is `1 - sin(p₁) ∫ φ dm`. -/
theorem inner_empty_residual_shifted (p : Fin 2 → ℝ) {phi : ℝ → ℝ}
    (hg : MemLp (fun x => -Complex.I * ((phi x : ℝ) : ℂ)) 2
      (volume.restrict (Set.Ioc (-Real.pi) Real.pi)))
    (kc : ℓ²(Manhattan.Type112Index, ℂ)) :
    inner ℂ (Manhattan.walshL2 ∅)
        (unnormalizedResidual p 1
          (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal
            (fourierBasis.repr (rowTorusShift (p 1)
              (Manhattan.realTorusL2 (fun x => -Complex.I * ((phi x : ℝ) : ℂ)) hg))))
          (Manhattan.type112WalshSynthesis kc))
      = ((1 - Real.sin (p 0) * Estimates.torusIntegral phi : ℝ) : ℂ) := by
  classical
  set c := fourierBasis.repr (rowTorusShift (p 1)
    (Manhattan.realTorusL2 (fun x => -Complex.I * ((phi x : ℝ) : ℂ)) hg)) with hc
  set f := Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal c with hf
  -- the degree-three part contributes nothing at the empty index
  have hk3 : inner ℂ (Manhattan.walshL2 ∅)
      (Manhattan.concreteFiberA p (Manhattan.type112WalshSynthesis kc)) = 0 :=
    inner_walshL2_concreteFiberA_eq_zero
      (Manhattan.type112WalshSynthesis_mem_degree kc) p (by simp) (by simp)
  -- the degree-one part
  have hc0 : c 0 = -Complex.I * ((Estimates.torusIntegral phi : ℝ) : ℂ) := by
    rw [hc, fourierBasis_repr_rowTorusShift_zero, fourierBasis_repr_realTorusL2_eq]
    have hchar : ∀ x : ℝ, intCharacter (-(0 : ℤ)) x = 1 := by
      intro x
      rw [neg_zero, intCharacter_index_zero]
    simp only [hchar, one_mul]
    have h1 : (Estimates.torusIntegral fun x => -Complex.I * ((phi x : ℝ) : ℂ))
        = -Complex.I * Estimates.torusIntegral (fun x => ((phi x : ℝ) : ℂ)) := by
      unfold Estimates.torusIntegral
      rw [integral_const_mul]
      simp only [Complex.real_smul]
      ring
    rw [h1, Energy.torusIntegral_ofReal phi]
  have hlow : loweringCoefficient p f ∅
      = -(Complex.I * (Real.sin (p 0) : ℂ)) * c 0 := dStarZero_axisDegreeOne p c
  have hf1 : inner ℂ (Manhattan.walshL2 ∅) (Manhattan.concreteFiberA p f)
      = ((Real.sin (p 0) * Estimates.torusIntegral phi : ℝ) : ℂ) := by
    have hneg := loweringCoefficient_eq_neg_inner p f ∅
    rw [hlow, hc0] at hneg
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    have : inner ℂ (Manhattan.walshL2 ∅) (Manhattan.concreteFiberA p f)
        = -(-(Complex.I * (Real.sin (p 0) : ℂ)) *
            (-Complex.I * ((Estimates.torusIntegral phi : ℝ) : ℂ))) := by
      rw [hneg]; ring
    rw [this]
    push_cast
    linear_combination (-(Complex.sin (p 0 : ℂ) *
      ((Estimates.torusIntegral phi : ℝ) : ℂ))) * hI
  rw [unnormalizedResidual, inner_sub_right, inner_smul_right, Manhattan.inner_walshL2,
    if_pos rfl, map_add, inner_add_right, hf1, hk3]
  push_cast
  ring

/-! ## Column periodicity of the competitor profile -/

variable {kappa delta : ℝ}

theorem parityProfileV_periodic_col {q : Estimates.Parameters} (hlam : 0 < q.lambda)
    (hkappa : 0 < kappa) (hdelta : 0 < delta) (w : ParityProfile)
    (hwcol : ∀ r, Function.Periodic (fun beta => w.toFun r beta) (2 * Real.pi))
    (r : ℝ) :
    Function.Periodic
      (fun beta => (parityProfileV hlam hkappa hdelta w).toFun r beta) (2 * Real.pi) := by
  intro beta
  have hw := hwcol r beta
  simp only at hw
  have hs : paritySigma kappa delta r (beta + 2 * Real.pi)
      = paritySigma kappa delta r beta := paritySigma_periodic_col kappa delta r beta
  have hd : Estimates.dispersion (beta + 2 * Real.pi) = Estimates.dispersion beta :=
    dispersion_periodic beta
  show parityV q kappa delta w.toFun r (beta + 2 * Real.pi)
    = parityV q kappa delta w.toFun r beta
  rw [parityV, parityV, hw, hs, Estimates.correctionB, Estimates.correctionB, hd]

theorem scaleProfile_periodic_col (cs : ℝ) (v : ParityProfile)
    (hvcol : ∀ r, Function.Periodic (fun beta => v.toFun r beta) (2 * Real.pi)) (r : ℝ) :
    Function.Periodic (fun beta => (scaleProfile cs v).toFun r beta) (2 * Real.pi) := by
  intro beta
  have h := hvcol r beta
  simp only at h
  show cs * v.toFun r (beta + 2 * Real.pi) = cs * v.toFun r beta
  rw [h]

/-! ## Move 1 as a competitor objective -/

/-- **Move 1 of Version 4, as a competitor objective.** This is
`Manhattan.V4.resolventQuadratic_le_v4Move1` one step earlier, before
`Manhattan.Operator.DissipativeSkewPair.resolventQuadratic_le` is applied, so
that the bound can be transported through the axis swap
(`Manhattan.Glue.axisSwap_competitorObjective`). -/
theorem objective_le_v4Move1 {lambda : ℝ} (hlambda : 0 < lambda)
    (p : Fin 2 → ℝ) {cc : ℝ} (c : Manhattan.RowLineCoefficient)
    (kc : ℓ²(Manhattan.Type112Index, ℂ))
    (hk : Manhattan.type112DStarTwoRow p kc = 0)
    (hc : inner ℂ (Manhattan.walshL2 ∅)
        (unnormalizedResidual p 1
          (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal c)
          (Manhattan.type112WalshSynthesis kc)) = ((cc : ℝ) : ℂ)) :
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hEnergy lambda
        (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal c
          + Manhattan.type112WalshSynthesis kc)
      + (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hlambda
          (Manhattan.walshL2 ∅ - Manhattan.concreteFiberA p
            (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal c
              + Manhattan.type112WalshSynthesis kc))
      ≤ cc ^ 2 / (lambda + Operator.theta p)
        + 2 * (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hEnergy
            lambda (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal c)
        + 2 * (sectorHThreeForm lambda p (Manhattan.type112WalshSynthesis kc)
            + sectorDFourForm hlambda p (Manhattan.type112WalshSynthesis kc))
        + 4 * (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy
            hlambda (Manhattan.type11WalshSynthesis (Manhattan.type11WalshAnalysis
              (walshRaise p
                (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal c))))
        + 4 * (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy
            hlambda (Manhattan.type12WalshSynthesis
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
      = Manhattan.walshL2 ∅ - Manhattan.concreteFiberA p
          (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal c
            + Manhattan.type112WalshSynthesis kc) := by
    rw [unnormalizedResidual, Complex.ofReal_one, one_smul]
  have hpar := hEnergy_add_le
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p) hlambda.le
    (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal c)
    (Manhattan.type112WalshSynthesis kc)
  have hsec := hMinusEnergy_residual_le hlambda p 1 hf hkk hc
  rw [hres] at hsec
  have hsplit := hMinusEnergy_sectorTwo_split hlambda p c kc hk
  have hH : sectorHThreeForm lambda p (Manhattan.type112WalshSynthesis kc)
      = (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hEnergy lambda
        (Manhattan.type112WalshSynthesis kc) := rfl
  have hD : sectorDFourForm hlambda p (Manhattan.type112WalshSynthesis kc)
      = (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy
        hlambda (walshSectorComponent (fun S => S.card = 4)
          (Manhattan.concreteFiberA p (Manhattan.type112WalshSynthesis kc))) := rfl
  rw [hH, hD]
  linarith

/-! ## Integrability of the Move 1 majorant -/

open Manhattan.V4.Frequency in
theorem effectiveWeight_perProfile_pointwise {r0 delta : ℝ}
    (hsq : 0 < Real.sqrt delta) (hr01 : r0 < 1) (hr0pi : r0 < Real.pi) (t : ℝ)
    {r : ℝ} (hr : r ∈ Estimates.torus) :
    Energy.effectiveWeight r * perProfile r0 delta t r ^ 2
      = t ^ 2 * perProfile r0 delta 1 r := by
  by_cases hmem : Real.sqrt delta ≤ |r| ∧ |r| ≤ r0
  · have hrpos : 0 < |r| := lt_of_lt_of_le hsq hmem.1
    have hrlt : |r| < 1 := lt_of_le_of_lt hmem.2 hr01
    rw [perProfile_eq_mul_logWeight hr0pi hmem.1 hmem.2,
      perProfile_eq_mul_logWeight (t := 1) hr0pi hmem.1 hmem.2,
      energyEffectiveWeight_eq, effectiveWeight, logWeight, one_mul]
    exact effectiveWeight_mul_sq hrpos hrlt
  · rw [perProfile_supp_torus hr hmem, perProfile_supp_torus (t := 1) hr hmem]
    ring

open Manhattan.V4.Frequency in
theorem integrable_effectiveWeight_perProfile {r0 delta : ℝ}
    (hsq : 0 < Real.sqrt delta) (hle : Real.sqrt delta ≤ r0) (hr01 : r0 < 1)
    (hr0pi : r0 < Real.pi) (t : ℝ) :
    Integrable (fun r => Energy.effectiveWeight r * perProfile r0 delta t r ^ 2)
      (volume.restrict Estimates.torus) := by
  have hbase : Integrable (fun r => t ^ 2 * perProfile r0 delta 1 r)
      (volume.restrict Estimates.torus) :=
    (integrableOn_perProfile hsq hle hr01 1).const_mul _
  refine hbase.congr ?_
  refine (ae_restrict_iff' Estimates.measurableSet_torus).mpr
    (Filter.Eventually.of_forall ?_)
  intro r hr
  exact (effectiveWeight_perProfile_pointwise hsq hr01 hr0pi t hr).symm

/-- Jordan's inequality in the form estimate (4) needs it. -/
theorem sin_sq_le_two_dispersion (x : ℝ) :
    Real.sin x ^ 2 ≤ 2 * Estimates.dispersion x := by
  have h := Real.sin_sq_add_cos_sq x
  have hc := Real.neg_one_le_cos x
  rw [Estimates.dispersion]
  nlinarith [Real.cos_le_one x]

/-! ## Move 1 of Version 4, assembled -/

open Manhattan.V4.Frequency in
/-- **Move 1 of Version 4, at the parity competitor.** For every `t` the
Version 4 competitor `(f_p, k_p)` built from the profile
`φ = perProfile r0 delta t` obeys the effective-energy inequality with
`h₀ = λ + θ(p)`, `s = sin p₁` and the absolute constant
`C = 60 + 40(π² + 60π³)`. -/
theorem v4_move1_objective {q : Estimates.Parameters} (hlam : 0 < q.lambda)
    (p : Fin 2 → ℝ) {delta r0 : ℝ}
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1) (hlamdelta : q.lambda ≤ delta)
    (hr014 : r0 ≤ 1 / 4) (hsqle : Real.sqrt delta ≤ r0)
    (hmud : q.lambda + Estimates.dispersion (p 0) ≤ delta ^ 2)
    (hp2 : |p 1| ≤ delta) (t : ℝ) :
    ∃ g : Manhattan.WalshL2,
      (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hEnergy q.lambda g
          + (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hlam
              (Manhattan.walshL2 ∅ - Manhattan.concreteFiberA p g)
        ≤ (1 - Real.sin (p 0) * (t * profileMass r0 delta)) ^ 2
              / (q.lambda + Operator.theta p)
            + (60 + 40 * (Real.pi ^ 2 + Real.pi ^ 3 * 120 / 2))
                * (t ^ 2 * profileMass r0 delta) := by
  classical
  have hpi := Real.pi_pos
  have hr01 : r0 < 1 := lt_of_le_of_lt hr014 (by norm_num)
  have hr0pi : r0 < Real.pi := by linarith [Real.pi_gt_three]
  have hsqpos : 0 < Real.sqrt delta := Real.sqrt_pos.mpr hdelta
  have h120 : (0:ℝ) < 120 := by norm_num
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
  -- (P3)
  have hkTwoRow : Manhattan.type112DStarTwoRow p kc = 0 :=
    type112DStarTwoRow_rawShiftTwist hK
      (fun r r' b => parityKernel_neg_col v r r' b) p
  -- the degree-zero coefficient
  have hcc := inner_empty_residual_shifted p hg kc
  refine ⟨Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal cco
    + Manhattan.type112WalshSynthesis kc, ?_⟩
  refine le_trans (objective_le_v4Move1 hlam p cco kc hkTwoRow hcc) ?_
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
  set JJ := Estimates.torusIntegral (fun r => Wr r ^ 2 * parityFibreJ q 120 delta r) with hJJdef
  -- (1) the degree-one energy
  have hE1 : (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hEnergy q.lambda
      (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal cco) ≤ 6 * E := by
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
    exact degreeOne_cost_le hmu hdelta hdelta1 hmud hr014 hsupp hint
  -- (2) the two-row sector
  have hE2 : (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hlam
      (Manhattan.type11WalshSynthesis (Manhattan.type11WalshAnalysis
        (walshRaise p (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal cco))))
      ≤ 12 * E := by
    have h := hMinusEnergy_twoRow_le hlam p g hg
    have hcongr : (fun r => ‖g r‖ ^ 2) = fun r => phi r ^ 2 := by
      funext r
      rw [hgnorm r, sq_abs]
    rw [hcongr] at h
    have h2 := twoRow_cost_le (mu := q.lambda + Estimates.dispersion (p 0))
      (s := Real.sin (p 0)) hmu hdelta hdelta1 hmud hsinsq hr014 hsupp hint
    rw [Estimates.torusIntegral_smul_left] at h2
    have hJ0 : (0:ℝ) ≤ Real.sin (p 0) ^ 2
        / Real.sqrt ((q.lambda + Estimates.dispersion (p 0))
          * (q.lambda + Estimates.dispersion (p 0) + 2)) := by positivity
    have hkey : 4 * (Real.sin (p 0) ^ 2
          / Real.sqrt ((q.lambda + Estimates.dispersion (p 0))
            * (q.lambda + Estimates.dispersion (p 0) + 2)))
        * Estimates.torusIntegral (fun r => phi r ^ 2) ≤ 12 * E := by
      have hrw : 2 * Real.sin (p 0) ^ 2
            / Real.sqrt ((q.lambda + Estimates.dispersion (p 0))
              * (q.lambda + Estimates.dispersion (p 0) + 2))
          = 2 * (Real.sin (p 0) ^ 2
            / Real.sqrt ((q.lambda + Estimates.dispersion (p 0))
              * (q.lambda + Estimates.dispersion (p 0) + 2))) := by ring
      rw [hrw] at h2
      linarith
    linarith
  -- (3) the degree-three cost
  have hE3 : sectorHThreeForm q.lambda p (Manhattan.type112WalshSynthesis kc)
      + sectorDFourForm hlam p (Manhattan.type112WalshSynthesis kc) ≤ 18 * JJ := by
    have hop := operatorEstimate_parityKernel hlam hdelta hlamdelta p hp2 v
    have hsc := paritySigmaEnergy_scaled_le (q := q) (kappa := 120) (delta := delta)
      hlam h120 hdelta hmw hbw
    have hveq : (fun beta => Estimates.torusIntegral (fun r =>
          paritySigma 120 delta r beta * v.toFun r beta ^ 2))
        = fun beta => Estimates.torusIntegral (fun r =>
          paritySigma 120 delta r beta
            * (Real.sqrt 2 * parityV q 120 delta (fun r' _ => Wr r') r beta) ^ 2) := rfl
    rw [hveq] at hop
    have hrw : rawWalsh p (torusBounded₃_parityKernel (by norm_num : (0:ℝ) < 120) hdelta v)
        = Manhattan.type112WalshSynthesis kc := rfl
    rw [hrw] at hop
    linarith
  -- (4) the mixed sector
  have hE4 : (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hlam
      (Manhattan.type12WalshSynthesis
        (Manhattan.type12WalshAnalysis (walshRaise p
            (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal cco))
          - Manhattan.type112DStarMixed p kc)) ≤ JJ := by
    have hden := hMinusEnergy_v4Mixed_density (q := q) hlam h120 hdelta v hvcol
      hgmeas hgb hgper hg p
    rw [hden]
    have hcongr : (fun r => Estimates.torusIntegral (fun beta =>
          ‖v4MixedSymbol 120 delta v.toFun g r beta‖ ^ 2 / Estimates.correctionB q r beta))
        = fun r => Estimates.torusIntegral (fun beta =>
          (Wr r - paritySigma 120 delta r beta
              * parityV q 120 delta (fun r' _ => Wr r') r beta) ^ 2
            / Estimates.correctionB q r beta) := by
      funext r
      congr 1
      funext beta
      have hvv : v.toFun r beta
          = Real.sqrt 2 * parityV q 120 delta (fun r' _ => Wr r') r beta := rfl
      rw [norm_v4MixedSymbol_sq 120 delta v phi r beta, hvv,
        inv_sqrt_two_mul_scaled]
    rw [hcongr]
    exact mixedResidual_integral_le hlam h120 hdelta hmw hbw
  -- (5) the Move 1 density
  have hE5 : 40 * JJ ≤ 40 * (Real.pi ^ 2 + Real.pi ^ 3 * 120 / 2) * E := by
    have h := v4_cost_le (q := q) (kappa := 120) (delta := delta) (r0 := r0)
      (C1 := 0) (C3 := 40) hlam h120 hdelta hr014 le_rfl (by norm_num) hsupp hint
    have hJJeq : JJ = Estimates.torusIntegral (fun r =>
        Real.sin r ^ 2 * parityFibreJ q 120 delta r * phi r ^ 2) := by
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
  linarith

end Manhattan.V4
