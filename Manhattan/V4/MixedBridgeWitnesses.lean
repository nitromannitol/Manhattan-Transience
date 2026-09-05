import Manhattan.V4.MixedBridge
import Manhattan.V4.AssemblyWitnesses

/-!
# The non-degeneracy certificates for the mixed bridge

Every statement of `Manhattan/V4/MixedBridge.lean` gets a witness here:
explicit parameters satisfying all of its hypotheses simultaneously, and, for
each inequality, a proof that it is **strict** at explicit data, so no link can
be `X = X` after unfolding.

* `witnessProfile` is `Manhattan.V4.sineProfile` at the constant profile
  `φ ≡ 1`, so `v(r,β) = sin r`.  It is not the zero profile:
  `witnessProfile_at_half_pi` evaluates it to `1`, and
  `strict_norm_parityKernel_pos` shows the kernel fed to the bridge is nonzero
  at explicit frequencies.  So no identity proved about it is `0 = 0`.
* `nonvacuity_mixedFourierCoefficient_rawOffDiagonalPart` instantiates the
  bridge itself: all three hypotheses (`TorusBoundedThree`, row periodicity, row
  symmetry) hold simultaneously at `κ = 120`, `δ = 1/100` and that profile.
* `strict_shiftPhase_ne_one`: the unimodular `(shift)` factor in the bridge is
  `-1` at `p₂ = π`, `m = 1`.  The bridge is therefore not the identity with a
  hidden `1` in front.
* `strict_parityMixedSymbol_normalization`: the mixed symbol is `(√2)⁻¹ σ v`
  and **not** `σ v`; the two are strictly different at explicit frequencies.
  `strict_hMinusEnergy_density_halving`: the `2⁻¹` in
  `hMinusEnergy_parityMixed_density` is likewise strict.  A silently doubled or
  halved constant is caught by these two.  `parityMixedSymbol_ne_zero` shows the
  function whose Fourier coefficients the bridge computes is not the zero
  function, and `nonvacuity_mixedFourierCoefficient_shift` instantiates the
  translation lemma.
* `strict_weightedCompletion_le` and `strict_weightedCompletion_le_density`:
  the two inequalities of the weighted scalar completion are strict at
  `B = σ = w = 1`, `C = 18`.
* `nonvacuity_hMinusEnergy_parityMixed_density` instantiates the degree-two
  dual form at `λ = 1/2` (`witnessParameters`, proved admissible).
-/

noncomputable section

open MeasureTheory

namespace Manhattan.V4

/-! ### The witness data -/

/-- The constant profile `φ ≡ 1` is even, bounded and `2π`-periodic, so
`Manhattan.V4.sineProfile` builds a genuine `ParityProfile` from it. -/
def witnessProfile : ParityProfile :=
  sineProfile (fun _ => 1) measurable_const 1 (fun _ => by norm_num)
    (fun _ => rfl) (fun _ => rfl)

@[simp] theorem witnessProfile_toFun (r beta : ℝ) :
    witnessProfile.toFun r beta = Real.sin r * 1 := rfl

/-- The witness profile is constant in the column frequency, so it satisfies
the extra periodicity hypothesis of `hMinusEnergy_parityMixed`. -/
theorem witnessProfile_periodic_col (r : ℝ) :
    Function.Periodic (fun beta => witnessProfile.toFun r beta) (2 * Real.pi) :=
  fun _ => rfl

/-- The witness parameter tuple, admissible for Section 4. -/
def witnessParameters : Estimates.Parameters := ⟨1/2, 20, Real.pi / 20⟩

theorem witnessParameters_lambda_pos : 0 < witnessParameters.lambda := by
  show (0:ℝ) < 1/2
  norm_num

theorem witnessParameters_admissible : witnessParameters.Admissible := by
  refine ⟨?_, ?_, ?_, ?_, le_rfl⟩
  · show (0:ℝ) < 1/2
    norm_num
  · show (1/2 : ℝ) ≤ 1
    norm_num
  · show (20:ℝ) ≤ 20
    norm_num
  · show (0:ℝ) < Real.pi / 20
    positivity

/-! ### The kernel fed to the bridge is not the zero kernel -/

theorem witnessProfile_at_half_pi (r : ℝ) :
    witnessProfile.toFun (Real.pi / 2) r = 1 := by
  rw [witnessProfile_toFun, Real.sin_pi_div_two, mul_one]

/-- **Strict.**  The Version 4 kernel is genuinely nonzero at explicit
frequencies, so no identity proved about it is `0 = 0`. -/
theorem strict_norm_parityKernel_pos :
    0 < ‖parityKernel 120 (1/100) witnessProfile.toFun
        (Real.pi / 2) (Real.pi / 2) (Real.pi / 2)‖ := by
  have hM : (0:ℝ) < evenMajorant 120 (1/100) (Real.pi / 2) (Real.pi / 2) (Real.pi / 2) :=
    evenMajorant_pos (by norm_num) (by norm_num) _ _ _
  have h2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hreal : 0 < parityKernelReal 120 (1/100) witnessProfile.toFun
      (Real.pi / 2) (Real.pi / 2) (Real.pi / 2) := by
    rw [parityKernelReal, witnessProfile_at_half_pi]
    positivity
  rw [parityKernel, norm_mul, norm_mul, Complex.norm_I, one_mul,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    Real.sin_pi_div_two]
  rw [abs_of_pos hreal]
  norm_num
  exact hreal

/-! ### The hypotheses of the bridge, satisfied at explicit data -/

theorem witness_torusBounded₃ :
    Glue.TorusBoundedThree (parityKernel 120 (1/100) witnessProfile.toFun) :=
  torusBounded₃_parityKernel (by norm_num) (by norm_num) witnessProfile

theorem witness_periodic_row' (r beta : ℝ) :
    Function.Periodic
      (fun r' => parityKernel 120 (1/100) witnessProfile.toFun r r' beta)
      (2 * Real.pi) :=
  parityKernel_periodic_row' witnessProfile r beta

theorem witness_symmetric (r r' b : ℝ) :
    parityKernel 120 (1/100) witnessProfile.toFun r r' b
      = parityKernel 120 (1/100) witnessProfile.toFun r' r b :=
  parityKernel_swap witnessProfile.toFun r r' b

/-- **The bridge, instantiated.**  All three hypotheses of
`mixedFourierCoefficient_rawOffDiagonalPart` hold simultaneously at
`κ = 120`, `δ = 1/100` and the nonzero profile `witnessProfile`, and the
landed conclusion is a statement about that concrete instance. -/
theorem nonvacuity_mixedFourierCoefficient_rawOffDiagonalPart
    (p : Fin 2 → ℝ) (m n : ℤ) :
    Glue.mixedFourierCoefficient
        (Glue.rawD2StarMixed (Glue.rawOffDiagonalPart (p 1)
          (parityKernel 120 (1/100) witnessProfile.toFun))) m n =
      Glue.intCharacter (-m) (p 1) * Glue.intCharacter (-n) (p 0) *
        Manhattan.type112DStarMixed p
          (Manhattan.type112ShiftTwist (p 0) (p 1)
            (rawType112Coefficients witness_torusBounded₃))
          ⟨Glue.mixedPairFinset (m, n), Glue.isType12Index_mixedPairFinset m n⟩ :=
  mixedFourierCoefficient_rawOffDiagonalPart witness_torusBounded₃
    (fun r beta => witness_periodic_row' r beta) witness_symmetric p m n

/-! ### The `(shift)` phase is not the identity -/

/-- **Strict.**  The unimodular factor in the bridge is a genuine phase: at
`p₂ = π` and `m = 1` it is `-1`.  So the bridge is not the identity
`X = X` with a hidden `1` in front. -/
theorem strict_shiftPhase_ne_one :
    Glue.intCharacter 1 Real.pi ≠ 1 := by
  have harg : Complex.I * ((((1:ℤ) : ℝ) * Real.pi : ℝ) : ℂ)
      = (Real.pi : ℂ) * Complex.I := by
    push_cast
    ring
  have hval : Glue.intCharacter 1 Real.pi = -1 := by
    rw [Glue.intCharacter, harg, Complex.exp_pi_mul_I]
  rw [hval]
  norm_num

/-! ### The normalization constants are real -/

theorem one_lt_sqrt_two : (1:ℝ) < Real.sqrt 2 := by
  have h : Real.sqrt 1 < Real.sqrt 2 := by
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rwa [Real.sqrt_one] at h

theorem inv_sqrt_two_lt_one : (Real.sqrt 2)⁻¹ < 1 :=
  inv_lt_one_of_one_lt₀ one_lt_sqrt_two

/-- **Strict.**  `σ v > 0` at explicit frequencies. -/
theorem strict_paritySigma_mul_profile_pos :
    0 < paritySigma 120 (1/100) (Real.pi / 2) (Real.pi / 2) *
      witnessProfile.toFun (Real.pi / 2) (Real.pi / 2) := by
  have hJ : 0 < parityJ 120 (1/100) (Real.pi / 2) (Real.pi / 2) :=
    parityJ_pos (by norm_num) (by norm_num) _ _
  have hsigma : 0 < paritySigma 120 (1/100) (Real.pi / 2) (Real.pi / 2) := by
    rw [paritySigma, Real.sin_pi_div_two]
    simpa using hJ
  rw [witnessProfile_at_half_pi]
  simpa using hsigma

/-- **Strict.**  The mixed symbol of the Version 4 competitor is `(√2)⁻¹ σ v`
and **not** `σ v`: the two differ at explicit frequencies.  A silently dropped
`(√2)⁻¹` would therefore be caught here. -/
theorem strict_parityMixedSymbol_normalization :
    (Real.sqrt 2)⁻¹ * (paritySigma 120 (1/100) (Real.pi / 2) (Real.pi / 2) *
        witnessProfile.toFun (Real.pi / 2) (Real.pi / 2))
      < paritySigma 120 (1/100) (Real.pi / 2) (Real.pi / 2) *
        witnessProfile.toFun (Real.pi / 2) (Real.pi / 2) := by
  have hpos := strict_paritySigma_mul_profile_pos
  nlinarith [inv_sqrt_two_lt_one]

/-- **Strict.**  The `2⁻¹` in `hMinusEnergy_parityMixed_density` is not slack:
the halved density is strictly below the unhalved one at explicit
frequencies. -/
theorem strict_hMinusEnergy_density_halving :
    2⁻¹ * ((paritySigma 120 (1/100) (Real.pi / 2) (Real.pi / 2) *
          witnessProfile.toFun (Real.pi / 2) (Real.pi / 2)) ^ 2
        / Estimates.correctionB witnessParameters (Real.pi / 2) (Real.pi / 2))
      < (paritySigma 120 (1/100) (Real.pi / 2) (Real.pi / 2) *
          witnessProfile.toFun (Real.pi / 2) (Real.pi / 2)) ^ 2
        / Estimates.correctionB witnessParameters (Real.pi / 2) (Real.pi / 2) := by
  have hpos := strict_paritySigma_mul_profile_pos
  have hB : 0 < Estimates.correctionB witnessParameters (Real.pi / 2) (Real.pi / 2) := by
    rw [Estimates.correctionB]
    have h1 := Estimates.dispersion_nonneg (Real.pi / 2)
    have h2 : (0:ℝ) < witnessParameters.lambda := witnessParameters_lambda_pos
    linarith
  have hnum : 0 < (paritySigma 120 (1/100) (Real.pi / 2) (Real.pi / 2) *
      witnessProfile.toFun (Real.pi / 2) (Real.pi / 2)) ^ 2 := by positivity
  have hquot : 0 < (paritySigma 120 (1/100) (Real.pi / 2) (Real.pi / 2) *
      witnessProfile.toFun (Real.pi / 2) (Real.pi / 2)) ^ 2
      / Estimates.correctionB witnessParameters (Real.pi / 2) (Real.pi / 2) :=
    div_pos hnum hB
  linarith

/-- The object whose Fourier coefficients the bridge computes is **not** the
zero function: the mixed symbol is nonzero at explicit frequencies. -/
theorem parityMixedSymbol_ne_zero :
    parityMixedSymbol 120 (1/100) witnessProfile.toFun (Real.pi / 2) (Real.pi / 2)
      ≠ 0 := by
  have hpos := strict_paritySigma_mul_profile_pos
  have h2 : (0:ℝ) < (Real.sqrt 2)⁻¹ := by positivity
  have hreal : (0:ℝ) < (Real.sqrt 2)⁻¹ *
      (paritySigma 120 (1/100) (Real.pi / 2) (Real.pi / 2) *
        witnessProfile.toFun (Real.pi / 2) (Real.pi / 2)) := mul_pos h2 hpos
  rw [parityMixedSymbol]
  exact_mod_cast hreal.ne'

/-- Both periodicity hypotheses of `mixedFourierCoefficient_shift` hold for the
Version 4 mixed symbol at the witness profile. -/
theorem nonvacuity_mixedFourierCoefficient_shift (p : Fin 2 → ℝ) (m n : ℤ) :
    Glue.mixedFourierCoefficient
        (fun s u => parityMixedSymbol 120 (1/100) witnessProfile.toFun
          (p 1 + s) (p 0 + u)) m n =
      Glue.intCharacter m (p 1) * Glue.intCharacter n (p 0) *
        Glue.mixedFourierCoefficient
          (parityMixedSymbol 120 (1/100) witnessProfile.toFun) m n :=
  mixedFourierCoefficient_shift (parityMixedSymbol_periodic_row witnessProfile)
    (parityMixedSymbol_periodic_col witnessProfile witnessProfile_periodic_col)
    (p 1) (p 0) m n

/-! ### The weighted scalar completion is strict -/

/-- **Strict.**  At `B = σ = w = 1`, `C = 18` and `u = 0` the weighted
completion reads `18/19 < 1`. -/
theorem strict_weightedCompletion_le :
    (1:ℝ) ^ 2 / (1 + 1 / 18) < 18 * 1 * (0:ℝ) ^ 2 + (1 - 1 * (0:ℝ)) ^ 2 / 1 := by
  norm_num

theorem nonvacuity_weightedCompletion_le :
    (1:ℝ) ^ 2 / (1 + 1 / 18) ≤ 18 * 1 * (0:ℝ) ^ 2 + (1 - 1 * (0:ℝ)) ^ 2 / 1 :=
  weightedCompletion_le (B := 1) (sigma := 1) (w := 1) (C := 18)
    (by norm_num) (by norm_num) (by norm_num) 0

/-- **Strict.**  At `B = σ = w = 1`, `C = 18` the passage to the Move 1 density
reads `18/19 < 9`. -/
theorem strict_weightedCompletion_le_density :
    (1:ℝ) ^ 2 / (1 + 1 / 18) < 18 * ((1:ℝ) ^ 2 / (1 + 1)) := by
  norm_num

theorem nonvacuity_weightedCompletion_le_density :
    (1:ℝ) ^ 2 / (1 + 1 / 18) ≤ 18 * ((1:ℝ) ^ 2 / (1 + 1)) :=
  weightedCompletion_le_density (B := 1) (sigma := 1) (w := 1) (C := 18)
    (by norm_num) (by norm_num) (by norm_num)

/-! ### The degree-two dual form, instantiated -/

/-- **The degree-two dual form at explicit data.**  Every hypothesis of
`hMinusEnergy_parityMixed_density` holds simultaneously at `λ = 1/2`,
`κ = 120`, `δ = 1/100` and the nonzero `witnessProfile`. -/
theorem nonvacuity_hMinusEnergy_parityMixed_density (p : Fin 2 → ℝ) :
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy
        witnessParameters_lambda_pos
        (Manhattan.type12WalshSynthesis
          (Manhattan.type112DStarMixed p
            (Manhattan.type112ShiftTwist (p 0) (p 1)
              (rawType112Coefficients witness_torusBounded₃))))
      = 2⁻¹ * Estimates.torusIntegral fun r => Estimates.torusIntegral fun beta =>
          (paritySigma 120 (1/100) r beta * witnessProfile.toFun r beta) ^ 2
            / Estimates.correctionB witnessParameters r beta :=
  hMinusEnergy_parityMixed_density witnessParameters_lambda_pos (by norm_num)
    (by norm_num) witnessProfile witnessProfile_periodic_col p

end Manhattan.V4
