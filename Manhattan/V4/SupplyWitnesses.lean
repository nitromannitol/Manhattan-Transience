import Manhattan.V4.Move2Supply

/-!
# Version 4, : the non-degeneracy record

The three failure modes this repository has shipped before -- `X ≤ X` after
unfolding, a hypothesis forcing the bounded quantity to vanish, and a clause
discharged because the datum passed in *was* the thing being characterised --
are checked individually for the four residues closed by this part.

**The witness data.**  `r₀ = 1/4`, `λ = 10⁻⁶`, `p = (10⁻³, 0)`.  Then
`√λ + a(p) = 1/500 ≤ (1/4)⁴ = 1/256`, so the witness frequency lies in the
improvement region where `V4Move2Supply` has content, and `sin p₁ ≠ 0`, so the
competitor is not the trivial one.

**The check that matters most** is `strict_v4Move2Supply_improves`: at the
witness frequency the Move 2 closed form is **strictly** below the driftless
bound `1/(λ + θ(p))`.  A chain that had collapsed to `X ≤ X` anywhere would
deliver only the driftless bound, so this single strict inequality rules out the
first failure mode for the whole composed chain.

The remaining entries check the individual links: `(B-1b)` is instantiated at a
coefficient equal to `2⁻¹` (`strict_mixedFourierCoefficient_raising`), so it is
not `0 = 0`; `(B-2)`'s `α`-average is strictly better than the pointwise weight
`1/μ` (`strict_twoRowWeightAverage_lt`); `(B-3)`'s exact additivity is strictly
stronger than the parallelogram bound it replaces
(`strict_hMinusEnergy_empty_add_lt_parallelogram`), which is exactly why
`V4Move2Supply` can carry the coefficient one on `λ + θ(p)`; and 's
recorded `effectiveWeight 0 = 0` hazard is harmless because the competitor
profile also vanishes at the origin (`perProfile_zero_at_origin`), while the
majorant as a whole is not zero (`strict_profileMass_pos`).
-/

noncomputable section
open MeasureTheory Set

namespace Manhattan.V4

open Manhattan.Glue Manhattan.Operator

/-! ## Explicit admissible data -/

/-- The radius used by the non-degeneracy witnesses. -/
def witnessR0 : ℝ := 1 / 4
/-- The spectral parameter used by the non-degeneracy witnesses. -/
def witnessLambda : ℝ := 1 / 1000000
/-- The frequency used by the non-degeneracy witnesses. -/
def witnessP : Fin 2 → ℝ := ![1 / 1000, 0]

theorem witnessLambda_pos : 0 < witnessLambda := by
  show (0:ℝ) < 1 / 1000000
  norm_num

theorem witnessLambda_le_one : witnessLambda ≤ 1 := by
  show (1:ℝ) / 1000000 ≤ 1
  norm_num

theorem sqrt_witnessLambda : Real.sqrt witnessLambda = 1 / 1000 := by
  have h : witnessLambda = (1 / 1000 : ℝ) ^ 2 := by
    show (1:ℝ) / 1000000 = (1 / 1000 : ℝ) ^ 2
    norm_num
  rw [h, Real.sqrt_sq (by norm_num)]

theorem witnessP_zero : witnessP 0 = 1 / 1000 := rfl
theorem witnessP_one : witnessP 1 = 0 := rfl

theorem maxFrequency_witnessP : Operator.maxFrequency witnessP = 1 / 1000 := by
  rw [Operator.maxFrequency, witnessP_zero, witnessP_one]
  rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 1000), abs_zero]
  exact max_eq_left (by norm_num)

theorem witnessP_mem_torus : witnessP 0 ∈ Manhattan.Estimates.torus := by
  rw [witnessP_zero]
  constructor
  · have := Real.pi_gt_three
    show -Real.pi < 1 / 1000
    linarith
  · have := Real.pi_gt_three
    show (1:ℝ) / 1000 ≤ Real.pi
    linarith

theorem witnessP_one_mem_torus : witnessP 1 ∈ Manhattan.Estimates.torus := by
  rw [witnessP_one]
  constructor
  · have := Real.pi_gt_three
    show -Real.pi < 0
    linarith
  · have := Real.pi_gt_three
    show (0:ℝ) ≤ Real.pi
    linarith

/-- The witness frequency lies in the improvement region. -/
theorem witness_improvement :
    Real.sqrt witnessLambda + Operator.maxFrequency witnessP ≤ witnessR0 ^ 4 := by
  rw [sqrt_witnessLambda, maxFrequency_witnessP]
  show (1:ℝ) / 1000 + 1 / 1000 ≤ (1 / 4 : ℝ) ^ 4
  norm_num

/-! ## The Move 2 supply, instantiated -/

/-- **`v4Move2Supply_proved` at explicit admissible data.**  The hypothesis set
of `Manhattan.V4.Frequency.V4Move2Supply` is satisfiable, so the theorem is a
statement about a concrete instance. -/
theorem nonvacuity_v4Move2Supply :
    ∃ s : ℝ, (2 / Real.pi) ^ 2 * Operator.maxFrequency witnessP ^ 2 ≤ s ^ 2 ∧
      (Manhattan.concreteFiberEnvironment.dissipativeSkewPair witnessP).resolventQuadratic
          witnessLambda_pos (Manhattan.walshL2 ∅)
        ≤ 1 / (witnessLambda + Operator.theta witnessP
            + s ^ 2 * Zdelta witnessR0
                (Real.sqrt witnessLambda + Operator.maxFrequency witnessP)
              / v4Constant) :=
  v4Move2Supply_proved (r0 := witnessR0) (by show (0:ℝ) < 1 / 4; norm_num)
    (by show (1:ℝ) / 4 ≤ 1 / 4; norm_num)
    witnessLambda witnessLambda_pos witnessLambda_le_one witnessP
    witnessP_mem_torus witnessP_one_mem_torus witness_improvement

theorem theta_witnessP_nonneg : 0 ≤ Operator.theta witnessP := by
  rw [Manhattan.Estimates.operator_theta_eq]
  exact Manhattan.Estimates.theta_nonneg witnessP

/-- **The Version 4 competitor does real work.**  At the witness frequency the
Move 2 closed form is **strictly** smaller than the driftless bound
`1/(λ + θ(p))`, so no link of the chain is an equality in disguise: a chain that
collapsed to `X ≤ X` would deliver only the driftless bound. -/
theorem strict_v4Move2Supply_improves :
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair witnessP).resolventQuadratic
        witnessLambda_pos (Manhattan.walshL2 ∅)
      < 1 / (witnessLambda + Operator.theta witnessP) := by
  obtain ⟨s, hs, hbound⟩ := nonvacuity_v4Move2Supply
  have hpi := Real.pi_pos
  have ha : Operator.maxFrequency witnessP = 1 / 1000 := maxFrequency_witnessP
  have hspos : 0 < s ^ 2 := by
    have h0 : (0:ℝ) < (2 / Real.pi) ^ 2 * Operator.maxFrequency witnessP ^ 2 := by
      rw [ha]
      positivity
    linarith
  have hdelta : (0:ℝ) < Real.sqrt witnessLambda + Operator.maxFrequency witnessP := by
    rw [sqrt_witnessLambda, ha]
    norm_num
  have hZ : 0 < Zdelta witnessR0
      (Real.sqrt witnessLambda + Operator.maxFrequency witnessP) :=
    Frequency.Zdelta_pos (by show (0:ℝ) < 1 / 4; norm_num)
      (by show (1:ℝ) / 4 ≤ 1 / 4; norm_num) hdelta witness_improvement
  have hh0 : 0 < witnessLambda + Operator.theta witnessP := by
    have := theta_witnessP_nonneg
    have := witnessLambda_pos
    linarith
  have hextra : 0 < s ^ 2 * Zdelta witnessR0
      (Real.sqrt witnessLambda + Operator.maxFrequency witnessP) / v4Constant := by
    have := v4Constant_pos
    positivity
  refine lt_of_le_of_lt hbound ?_
  rw [div_lt_div_iff₀ (by linarith) hh0]
  linarith

/-- The same, spelled with the sealed driftless majorant of
`Manhattan.Glue.concrete_resolventQuadratic_le_driftless`: the Version 4
competitor strictly beats the bound that needs no competitor at all. -/
theorem strict_v4_beats_driftless :
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair witnessP).resolventQuadratic
        witnessLambda_pos (Manhattan.walshL2 ∅)
      < Operator.driftlessMajorant witnessLambda witnessP :=
  strict_v4Move2Supply_improves

/-! ## (B-1b) instantiated at a nonzero coefficient -/

/-- The constant row profile, a legitimate `2π`-periodic degree-one profile. -/
@[nolint unusedArguments]
def unitProfile : ℝ → ℂ := fun _ => 1

theorem unitProfile_periodic : Function.Periodic unitProfile (2 * Real.pi) :=
  fun _ => rfl

theorem unitProfile_memLp :
    MemLp unitProfile 2 (volume.restrict (Set.Ioc (-Real.pi) Real.pi)) := by
  have h : MemLp unitProfile 2 (volume.restrict Manhattan.Estimates.torus) := by
    refine MemLp.of_bound measurable_const.aestronglyMeasurable 1 ?_
    filter_upwards with x
    show ‖(1:ℂ)‖ ≤ 1
    simp
  exact h

/-- The zero frequency, at which the shift phase is trivial. -/
def zeroP : Fin 2 → ℝ := ![0, 0]

@[simp] theorem zeroP_zero : zeroP 0 = 0 := rfl
@[simp] theorem zeroP_one : zeroP 1 = 0 := rfl

theorem fourier_unitProfile (k : ℤ) :
    fourierBasis.repr (rowTorusShift (zeroP 1)
        (Manhattan.realTorusL2 unitProfile unitProfile_memLp)) k
      = if k = 0 then 1 else 0 := by
  rw [fourierBasis_repr_rowTorusShift, zeroP_one, intCharacter_zero, one_mul,
    fourierBasis_repr_realTorusL2_eq]
  have hbody : (fun x : ℝ => intCharacter (-k) x * unitProfile x)
      = intCharacter (-k) := by
    funext x
    show intCharacter (-k) x * 1 = intCharacter (-k) x
    ring
  rw [hbody, torusIntegral_intCharacter']
  by_cases hk : k = 0
  · rw [if_pos hk, hk]
    norm_num
  · rw [if_neg hk, if_neg (by omega : ¬ (-k = 0))]

/-- **(B-1b) is not `0 = 0`.**  At the constant row profile and the zero
frequency the common value of the two sides of
`Manhattan.V4.mixedFourierCoefficient_raising` is `2⁻¹`. -/
theorem strict_mixedFourierCoefficient_raising :
    mixedFourierCoefficient
        (fun s _ => Complex.I * (Real.sin (zeroP 1 + s) : ℂ) * unitProfile (zeroP 1 + s))
        1 0 = (2 : ℂ)⁻¹ := by
  rw [mixedFourierCoefficient_raising unitProfile_periodic unitProfile_memLp 1 0,
    Manhattan.type12WalshAnalysis, Manhattan.walshSectorAnalysis_apply,
    inner_mixedPair_walshRaise_axisDegreeOne zeroP _ 1 0, if_pos rfl,
    fourier_unitProfile, fourier_unitProfile, zeroP_one]
  norm_num

theorem strict_mixedFourierCoefficient_raising_ne_zero :
    mixedFourierCoefficient
        (fun s _ => Complex.I * (Real.sin (zeroP 1 + s) : ℂ) * unitProfile (zeroP 1 + s))
        1 0 ≠ 0 := by
  rw [strict_mixedFourierCoefficient_raising]
  norm_num

/-! ## (B-3): exact additivity is strictly stronger than the parallelogram bound -/

theorem hMinusEnergy_zero {lambda : ℝ} (hlambda : 0 < lambda) (p : Fin 2 → ℝ) :
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hlambda 0
      = 0 := by
  rw [Manhattan.Operator.DissipativeSkewPair.hMinusEnergy, map_zero, inner_zero_left]
  simp

/-- **The degree-zero sector really is additive, not parallelogram-bounded.**
The parallelogram bound `Manhattan.Glue.hMinusEnergy_add_le` would give twice
this value, and `Manhattan.V4.Frequency.V4Move2Supply` cannot absorb the factor
two on `λ + θ(p)`. -/
theorem strict_hMinusEnergy_empty_add_lt_parallelogram :
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair witnessP).hMinusEnergy
        witnessLambda_pos (((1 : ℝ) : ℂ) • Manhattan.walshL2 ∅ + 0)
      < 2 * (Manhattan.concreteFiberEnvironment.dissipativeSkewPair witnessP).hMinusEnergy
            witnessLambda_pos (((1 : ℝ) : ℂ) • Manhattan.walshL2 ∅)
        + 2 * (Manhattan.concreteFiberEnvironment.dissipativeSkewPair witnessP).hMinusEnergy
            witnessLambda_pos 0 := by
  have hh0 : 0 < witnessLambda + Operator.theta witnessP := by
    have := theta_witnessP_nonneg
    have := witnessLambda_pos
    linarith
  have hzero : inner ℂ (Manhattan.walshL2 ∅) (0 : Manhattan.WalshL2) = 0 := inner_zero_right _
  rw [hMinusEnergy_empty_add witnessLambda_pos witnessP 1 hzero,
    hMinusEnergy_degreeZero witnessLambda_pos witnessP, hMinusEnergy_zero]
  rw [Complex.norm_real, Real.norm_eq_abs]
  have h1 : |(1:ℝ)| = 1 := abs_one
  rw [h1]
  have hpos : 0 < (1:ℝ) ^ 2 / (witnessLambda + Operator.theta witnessP) := by positivity
  linarith

/-! ## (B-2): the `α`-average is strictly better than the pointwise weight -/

/-- The line resolvent `J(μ) = 1/√(μ(μ+2))` is **strictly** smaller than the
pointwise weight bound `1/μ` that the sealed docstring of
`Manhattan.Glue.hMinusEnergy_twoRowRaiseCoeff_le` says "cannot give" the
estimate.  So `twoRowWeightAverage_eq` is not a restatement of the trivial
bound. -/
theorem strict_twoRowWeightAverage_lt :
    twoRowWeightAverage ⟨1, 20, Real.pi / 20⟩ 0
      < ((1 : ℝ) + Manhattan.Estimates.dispersion 0)⁻¹ := by
  have hlam : (0:ℝ) < (⟨1, 20, Real.pi / 20⟩ : Manhattan.Estimates.Parameters).lambda := by
    show (0:ℝ) < 1
    norm_num
  rw [twoRowWeightAverage_eq hlam 0]
  have hd : Manhattan.Estimates.dispersion 0 = 0 := by
    rw [Manhattan.Estimates.dispersion, Real.cos_zero]
    ring
  have hlam1 : (⟨1, 20, Real.pi / 20⟩ : Manhattan.Estimates.Parameters).lambda = 1 := rfl
  rw [hd, hlam1]
  norm_num
  have h3 : (1:ℝ) < Real.sqrt 3 := by
    have h := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
    nlinarith [Real.sqrt_nonneg 3]
  have h3pos : (0:ℝ) < Real.sqrt 3 := by linarith
  rw [inv_lt_one_iff₀]
  right
  exact h3

/-! ## The scalar bounds are strict -/

theorem strict_v4_residual_le :
    (1 - 1 * (1 / (1 + 1))) ^ 2 / 1 < (1:ℝ) ^ 2 / (1 + 1) := by norm_num

theorem strict_v4_sigmaEnergy_le :
    (1:ℝ) * (1 / (1 + 1)) ^ 2 < (1:ℝ) ^ 2 / (1 + 1) := by norm_num

theorem nonvacuity_v4_residual_le :
    (1 - 1 * (1 / (1 + 1))) ^ 2 / 1 ≤ (1:ℝ) ^ 2 / (1 + 1) :=
  v4_residual_le (by norm_num) (by norm_num)

theorem nonvacuity_v4_sigmaEnergy_le :
    (1:ℝ) * (1 / (1 + 1)) ^ 2 ≤ (1:ℝ) ^ 2 / (1 + 1) :=
  v4_sigmaEnergy_le (by norm_num) (by norm_num)

/-! ## The recorded hazards -/

/-- recorded hazard: the effective weight vanishes at the origin. -/
theorem effectiveWeight_zero : Energy.effectiveWeight 0 = 0 := by
  rw [Energy.effectiveWeight]
  simp

/-- The hazard is harmless: the competitor profile also vanishes at the origin,
because `0 ∉ Γ_δ`, so the Move 1 majorant `q(r) φ(r)²` is `0 · 0` there and not a
junk value. -/
theorem perProfile_zero_at_origin {r0 delta t : ℝ} (hdelta : 0 < delta) :
    perProfile r0 delta t 0 = 0 := by
  refine perProfile_supp_torus ?_ ?_
  · exact ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  · intro h
    have h1 : Real.sqrt delta ≤ |(0:ℝ)| := h.1
    rw [abs_zero] at h1
    exact absurd h1 (not_le.mpr (Real.sqrt_pos.mpr hdelta))

/-- The Move 1 majorant is **not** forced to zero: the torus mass of the
competitor profile is strictly positive at the witness data. -/
theorem strict_profileMass_pos :
    0 < profileMass witnessR0 (Real.sqrt witnessLambda + Operator.maxFrequency witnessP) := by
  have hdelta : (0:ℝ) < Real.sqrt witnessLambda + Operator.maxFrequency witnessP := by
    rw [sqrt_witnessLambda, maxFrequency_witnessP]
    norm_num
  have hZ : 0 < Zdelta witnessR0
      (Real.sqrt witnessLambda + Operator.maxFrequency witnessP) :=
    Frequency.Zdelta_pos (by show (0:ℝ) < 1 / 4; norm_num)
      (by show (1:ℝ) / 4 ≤ 1 / 4; norm_num) hdelta witness_improvement
  have hr01 : (witnessR0 : ℝ) < 1 := by show (1:ℝ) / 4 < 1; norm_num
  have hr0pi : (witnessR0 : ℝ) < Real.pi := by
    have := Real.pi_gt_three
    show (1:ℝ) / 4 < Real.pi
    linarith
  have hsqle : Real.sqrt (Real.sqrt witnessLambda + Operator.maxFrequency witnessP)
      ≤ witnessR0 :=
    Frequency.sqrt_le_of_le_pow_four (by show (0:ℝ) < 1 / 4; norm_num)
      (by show (1:ℝ) / 4 ≤ 1 / 4; norm_num) witness_improvement
  exact lt_of_lt_of_le hZ
    (Zdelta_le_profileMass (Real.sqrt_pos.mpr hdelta) hsqle hr01 hr0pi)

/-- The composed Move 1 constant is a genuine finite absolute constant, strictly
bigger than the degree-one constant `C₁ = 60`: the degree-two and degree-three
sectors really contribute. -/
theorem strict_sixty_lt_v4Constant : (60 : ℝ) < v4Constant := by
  have := Real.pi_pos
  unfold v4Constant
  nlinarith [Real.pi_gt_three]

/-! ## The mixed sector, instantiated -/

/-- An honest `ParityProfile`: `v(r,β) = sin r`, odd in the row frequency, even
(constant) in the column frequency, `2π`-periodic. -/
def witnessV : ParityProfile :=
  sineProfile (fun _ => 1) measurable_const 1 (fun _ => by norm_num)
    (fun _ => rfl) (fun _ => rfl)

@[simp] theorem witnessV_toFun (r beta : ℝ) : witnessV.toFun r beta = Real.sin r * 1 := rfl

theorem unitProfile_norm_le (r : ℝ) : ‖unitProfile r‖ ≤ 1 := by
  show ‖(1:ℂ)‖ ≤ 1
  simp

theorem witnessQ_lambda_pos : (0:ℝ) < (v4Parameters 1).lambda := by
  show (0:ℝ) < 1
  norm_num

/-- **The degree-two dual form of the whole mixed sector, at explicit data.**
Every hypothesis of `Manhattan.V4.hMinusEnergy_v4Mixed_density` is satisfiable
simultaneously. -/
theorem nonvacuity_hMinusEnergy_v4Mixed_density :
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair witnessP).hMinusEnergy
        witnessQ_lambda_pos
        (Manhattan.type12WalshSynthesis
          (Manhattan.type12WalshAnalysis
              (walshRaise witnessP
                (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal
                  (fourierBasis.repr (rowTorusShift (witnessP 1)
                    (Manhattan.realTorusL2 unitProfile unitProfile_memLp)))))
            - Manhattan.type112DStarMixed witnessP
                (Manhattan.type112ShiftTwist (witnessP 0) (witnessP 1)
                  (rawType112Coefficients (torusBounded₃_parityKernel
                    (by norm_num : (0:ℝ) < 120)
                    (by norm_num : (0:ℝ) < 1 / 100) witnessV)))))
      = Manhattan.Estimates.torusIntegral fun r =>
          Manhattan.Estimates.torusIntegral fun beta =>
            ‖v4MixedSymbol 120 (1 / 100) witnessV.toFun unitProfile r beta‖ ^ 2
              / Manhattan.Estimates.correctionB (v4Parameters 1) r beta :=
  hMinusEnergy_v4Mixed_density (q := v4Parameters 1) witnessQ_lambda_pos
    (by norm_num) (by norm_num) witnessV (fun _ _ => rfl) measurable_const
    unitProfile_norm_le unitProfile_periodic unitProfile_memLp witnessP

/-- **The mixed symbol is not the zero function.**  At `(r,β) = (π/2, 0)` the
lowering half vanishes (`σ(r,0) = sin²(0) J = 0`) and the raising half is `i`, so
the density integrated by `hMinusEnergy_v4Mixed_density` is not identically
zero. -/
theorem strict_v4MixedSymbol_ne_zero :
    v4MixedSymbol 120 (1 / 100) witnessV.toFun unitProfile (Real.pi / 2) 0 ≠ 0 := by
  have hsig : paritySigma 120 (1 / 100) (Real.pi / 2) 0 = 0 := by
    rw [paritySigma, Real.sin_zero]
    ring
  have hval : v4MixedSymbol 120 (1 / 100) witnessV.toFun unitProfile (Real.pi / 2) 0
      = Complex.I := by
    rw [v4MixedSymbol, parityMixedSymbol, hsig]
    show Complex.I * ((Real.sin (Real.pi / 2) : ℝ) : ℂ) * 1
      - (((Real.sqrt 2)⁻¹ * (0 * witnessV.toFun (Real.pi / 2) 0) : ℝ) : ℂ) = Complex.I
    rw [Real.sin_pi_div_two]
    push_cast
    ring
  rw [hval]
  exact Complex.I_ne_zero

/-! ## (P3) and Move 1, instantiated -/

theorem nonvacuity_type112DStarTwoRow :
    Manhattan.type112DStarTwoRow witnessP
        (Manhattan.type112ShiftTwist (witnessP 0) (witnessP 1)
          (rawType112Coefficients (torusBounded₃_parityKernel
            (by norm_num : (0:ℝ) < 120) (by norm_num : (0:ℝ) < 1 / 100) witnessV))) = 0 :=
  type112DStarTwoRow_rawShiftTwist _
    (fun r r' b => parityKernel_neg_col witnessV r r' b) witnessP

theorem witnessP_abs_le_pi : |witnessP 0| ≤ Real.pi := by
  rw [witnessP_zero, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 1000)]
  have := Real.pi_gt_three
  linarith

/-- **Move 1 at explicit data**, for every profile parameter `t`. -/
theorem nonvacuity_v4_move1_at (t : ℝ) :
    ∃ g : Manhattan.WalshL2,
      (Manhattan.concreteFiberEnvironment.dissipativeSkewPair witnessP).hEnergy
            witnessLambda g
          + (Manhattan.concreteFiberEnvironment.dissipativeSkewPair
              witnessP).hMinusEnergy witnessLambda_pos
              (Manhattan.walshL2 ∅ - Manhattan.concreteFiberA witnessP g)
        ≤ (1 - Real.sin (witnessP 0)
                * (t * profileMass witnessR0
                    (Real.sqrt witnessLambda + Operator.maxFrequency witnessP))) ^ 2
              / (witnessLambda + Operator.theta witnessP)
            + v4Constant * (t ^ 2 * profileMass witnessR0
                (Real.sqrt witnessLambda + Operator.maxFrequency witnessP)) :=
  v4_move1_at witnessLambda_pos witnessLambda_le_one witnessP
    (by show (0:ℝ) < 1 / 4; norm_num) (by show (1:ℝ) / 4 ≤ 1 / 4; norm_num)
    witnessP_abs_le_pi witness_improvement t

/-! ## (B-2), instantiated -/

theorem nonvacuity_hMinusEnergy_twoRow_le :
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair witnessP).hMinusEnergy
        witnessQ_lambda_pos
        (Manhattan.type11WalshSynthesis (Manhattan.type11WalshAnalysis
          (walshRaise witnessP (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal
            (fourierBasis.repr (rowTorusShift (witnessP 1)
              (Manhattan.realTorusL2 unitProfile unitProfile_memLp)))))))
      ≤ 4 * (Real.sin (witnessP 0) ^ 2
            / Real.sqrt (((v4Parameters 1).lambda
                  + Manhattan.Estimates.dispersion (witnessP 0))
                * ((v4Parameters 1).lambda
                  + Manhattan.Estimates.dispersion (witnessP 0) + 2)))
          * Manhattan.Estimates.torusIntegral (fun r => ‖unitProfile r‖ ^ 2) :=
  hMinusEnergy_twoRow_le witnessQ_lambda_pos witnessP unitProfile unitProfile_memLp

/-- **The two-row bound does not force the sector energy to vanish.**  Its
right-hand side is strictly positive at the witness data, so
`hMinusEnergy_twoRow_le` is not a disguised `X ≤ 0`. -/
theorem strict_twoRow_bound_pos :
    0 < 4 * (Real.sin (witnessP 0) ^ 2
          / Real.sqrt (((v4Parameters 1).lambda
                + Manhattan.Estimates.dispersion (witnessP 0))
              * ((v4Parameters 1).lambda
                + Manhattan.Estimates.dispersion (witnessP 0) + 2)))
        * Manhattan.Estimates.torusIntegral (fun r => ‖unitProfile r‖ ^ 2) := by
  have hpi := Real.pi_gt_three
  have hsin : 0 < Real.sin (witnessP 0) := by
    rw [witnessP_zero]
    exact Real.sin_pos_of_pos_of_lt_pi (by norm_num) (by linarith)
  have hmass : Manhattan.Estimates.torusIntegral (fun r => ‖unitProfile r‖ ^ 2) = 1 := by
    have hbody : (fun r : ℝ => ‖unitProfile r‖ ^ 2) = fun _ : ℝ => (1:ℝ) := by
      funext r
      show ‖(1:ℂ)‖ ^ 2 = 1
      simp
    rw [hbody, Manhattan.Estimates.torusIntegral_const']
  have hlam1 : (v4Parameters 1).lambda = 1 := rfl
  have hd : 0 ≤ Manhattan.Estimates.dispersion (witnessP 0) :=
    Manhattan.Estimates.dispersion_nonneg _
  have hsqrt : 0 < Real.sqrt (((v4Parameters 1).lambda
        + Manhattan.Estimates.dispersion (witnessP 0))
      * ((v4Parameters 1).lambda + Manhattan.Estimates.dispersion (witnessP 0) + 2)) := by
    rw [hlam1]
    apply Real.sqrt_pos.mpr
    nlinarith
  rw [hmass, mul_one]
  positivity

end Manhattan.V4
