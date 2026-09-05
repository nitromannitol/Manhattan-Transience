import Manhattan.V4.Sectors

/-!
# Version 4, Move 1: the degree-two mixed sector (residue B-1b)

the formalization closed B-1, the raw-to-Walsh bridge for the **lowering** half
`(D₂*k)₁₂`, and recorded the **raising** half as the new residue B-1b. This
file closes it and assembles the whole mixed sector.

* `mixedRaising_rowFourier` is `Manhattan.Glue.mixedResidual_rowFourier` with
  the corrected competitor's `degreeOneCoefficient` replaced by an arbitrary
  `2π`-periodic row profile `g`, and the compact-support translation
  (`torusIntegral_translate_window`) replaced by the periodic one.
* `mixedFourierCoefficient_raising` is B-1b: the `(m,n)` mixed Fourier
  coefficient of the degree-one symbol `w(r) = i sin(r) g(r)`, read at the
  shifted row frequency, **is** the `(m,n)` mixed Walsh coefficient of `D₁f_p`.
* `type12WalshAnalysis_walshRaise_eq` is the same with the phase moved across,
  the shape the formalization recorded — **with two corrections**, see below.
* `type12FreqFun_v4Mixed` and `hMinusEnergy_v4Mixed_density` put the raising
  half together with lowering half and evaluate the degree-two dual
  form of the whole mixed sector as `∫∫ ‖w - (√2)⁻¹σv‖²/B`.

**Two corrections to the goal state.**
That goal state is false as elaborated in `scratch/V4D_probe.lean`.

1. The degree-one competitor must be the **shifted** row synthesis
   `axisDegreeOneSynthesis horizontal (fourierBasis.repr (rowTorusShift (p 1) …))`,
   not `degreeOneRealFrequencySynthesis`. This is forced anyway: it is the
   vector whose degree-one energy `Manhattan.Glue.hEnergy_degreeOneRowShift`
   evaluates, and `Manhattan.Glue.fourierBasis_repr_rowTorusShift_zero` shows the
   shift does not change the degree-zero coefficient, so Move 1's numerator
   `1 - sin(p₁)∫φ` is unaffected.
2. The phase is `intCharacter m (p 1) * intCharacter n (p 0)`, not
   `intCharacter (-m) (p 1) * intCharacter (-n) (p 0)`. This is the same phase
   `Manhattan.V4.type112DStarMixed_parityKernel` carries on the lowering half,
   which is what makes the two halves subtract. With the unshifted synthesis
   and the inverted phase the two sides differ already at `m = n = 0`, by
   `e^{i p₂}`.
-/

noncomputable section
open MeasureTheory Set

namespace Manhattan.V4

open Manhattan.Glue


/-- **The row Fourier coefficient of the mixed component of `D₁f_p`, for a
general `2π`-periodic row profile.** This is
`Manhattan.Glue.mixedResidual_rowFourier` with the corrected competitor's
`degreeOneCoefficient` replaced by an arbitrary periodic profile, and the
compact-support translation replaced by the periodic one. -/
theorem mixedRaising_rowFourier {p : Fin 2 → ℝ} {g : ℝ → ℂ}
    (hgper : Function.Periodic g (2 * Real.pi))
    (hg : MemLp g 2 (volume.restrict (Ioc (-Real.pi) Real.pi))) (m : ℤ) :
    (Estimates.torusIntegral fun s =>
        intCharacter (-m) s * (Complex.I * (Real.sin (p 1 + s) : ℂ) * g (p 1 + s)))
      = (2 : ℂ)⁻¹ *
        (Complex.exp (Complex.I * (p 1 : ℂ)) *
            fourierBasis.repr (rowTorusShift (p 1) (Manhattan.realTorusL2 g hg)) (m - 1) -
          Complex.exp (-Complex.I * (p 1 : ℂ)) *
            fourierBasis.repr (rowTorusShift (p 1) (Manhattan.realTorusL2 g hg)) (m + 1)) := by
  classical
  have hgint : Integrable g (volume.restrict Estimates.torus) := by
    rw [Estimates.torus]
    exact hg.integrable (by norm_num)
  have hchint : ∀ k : ℤ, Integrable (fun r => intCharacter (-k) r * g r)
      (volume.restrict Estimates.torus) :=
    fun k => hgint.bdd_mul (c := 1)
      (measurable_intCharacter (-k)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => le_of_eq (norm_intCharacter _ _))
  have hshift : ∀ s : ℝ,
      intCharacter (-m) s * (Complex.I * (Real.sin (p 1 + s) : ℂ) * g (p 1 + s))
        = intCharacter m (p 1) *
          (intCharacter (-m) (p 1 + s) *
            (Complex.I * (Real.sin (p 1 + s) : ℂ) * g (p 1 + s))) := by
    intro s
    rw [intCharacter_shift m (p 1) s]
    ring
  simp only [hshift]
  rw [torusIntegral_const_mul]
  have hper : Function.Periodic
      (fun r : ℝ => intCharacter (-m) r * (Complex.I * (Real.sin r : ℂ) * g r))
      (2 * Real.pi) := by
    intro r
    show intCharacter (-m) (r + 2 * Real.pi) *
        (Complex.I * (Real.sin (r + 2 * Real.pi) : ℂ) * g (r + 2 * Real.pi))
      = intCharacter (-m) r * (Complex.I * (Real.sin r : ℂ) * g r)
    rw [intCharacter_periodic, Real.sin_add_two_pi, hgper r]
  rw [torusIntegral_translate_periodic (E := ℂ) hper (p 1)]
  have hsplit : ∀ r : ℝ, intCharacter (-m) r * (Complex.I * (Real.sin r : ℂ) * g r) =
      (2 : ℂ)⁻¹ * (intCharacter (-(m - 1)) r * g r) -
        (2 : ℂ)⁻¹ * (intCharacter (-(m + 1)) r * g r) := by
    intro r
    linear_combination (-(g r)) * intCharacter_mul_neg_I_sin m r
  simp only [hsplit]
  rw [torusIntegral_sub ((hchint (m - 1)).const_mul _) ((hchint (m + 1)).const_mul _),
    torusIntegral_const_mul, torusIntegral_const_mul,
    fourierBasis_repr_rowTorusShift, fourierBasis_repr_rowTorusShift,
    fourierBasis_repr_realTorusL2_eq, fourierBasis_repr_realTorusL2_eq,
    ← intCharacter_one_eq, ← intCharacter_neg_one_eq]
  set X : ℂ := Estimates.torusIntegral fun x => intCharacter (-(m - 1)) x * g x with hX
  set Y : ℂ := Estimates.torusIntegral fun x => intCharacter (-(m + 1)) x * g x with hY
  have e1 : intCharacter 1 (p 1) * intCharacter (m - 1) (p 1) = intCharacter m (p 1) := by
    rw [intCharacter_add_index]
    congr 1
    ring
  have e2 : intCharacter (-1) (p 1) * intCharacter (m + 1) (p 1) = intCharacter m (p 1) := by
    rw [intCharacter_add_index]
    congr 1
    ring
  linear_combination (-(2 : ℂ)⁻¹ * X) * e1 + ((2 : ℂ)⁻¹ * Y) * e2

/-- **(B-1b) The raising half of the degree-two mixed sector.** The `(m,n)`
mixed Fourier coefficient of the degree-one symbol `w(r) = i sin(r) g(r)`, read
at the shifted row frequency of `(shift)`, is exactly the `(m,n)` mixed Walsh
coefficient of `D₁f_p`. The symbol does not depend on the column frequency,
which is why the coefficient is carried entirely by `n = 0`. -/
theorem mixedFourierCoefficient_raising {p : Fin 2 → ℝ} {g : ℝ → ℂ}
    (hgper : Function.Periodic g (2 * Real.pi))
    (hg : MemLp g 2 (volume.restrict (Ioc (-Real.pi) Real.pi))) (m n : ℤ) :
    mixedFourierCoefficient
        (fun s _ => Complex.I * (Real.sin (p 1 + s) : ℂ) * g (p 1 + s)) m n
      = Manhattan.type12WalshAnalysis
          (walshRaise p (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal
            (fourierBasis.repr (rowTorusShift (p 1) (Manhattan.realTorusL2 g hg)))))
          ⟨mixedPairFinset (m, n), isType12Index_mixedPairFinset m n⟩ := by
  classical
  have hinner : ∀ s : ℝ,
      (Estimates.torusIntegral fun u => intCharacter (-m) s * intCharacter (-n) u *
          (Complex.I * (Real.sin (p 1 + s) : ℂ) * g (p 1 + s)))
        = (intCharacter (-m) s *
            (Complex.I * (Real.sin (p 1 + s) : ℂ) * g (p 1 + s)))
          * (if n = 0 then (1 : ℂ) else 0) := by
    intro s
    have hpt : ∀ u : ℝ,
        intCharacter (-m) s * intCharacter (-n) u *
            (Complex.I * (Real.sin (p 1 + s) : ℂ) * g (p 1 + s))
          = (intCharacter (-m) s *
              (Complex.I * (Real.sin (p 1 + s) : ℂ) * g (p 1 + s)))
            * intCharacter (-n) u := by
      intro u; ring
    simp only [hpt]
    rw [torusIntegral_const_mul]
    congr 1
    rw [torusIntegral_intCharacter']
    simp
  rw [mixedFourierCoefficient]
  simp only [hinner]
  rw [torusIntegral_mul_const, mixedRaising_rowFourier hgper hg m,
    Manhattan.type12WalshAnalysis, Manhattan.walshSectorAnalysis_apply,
    inner_mixedPair_walshRaise_axisDegreeOne p _ m n]
  by_cases hn : n = 0 <;> simp [hn]

/-- **(B-1b), with the shift phase moved across.** This is the shape the formalization
recorded, with the two corrections that shape needs: the degree-one competitor
is the **shifted** row synthesis (the one `Manhattan.Glue.hEnergy_degreeOneRowShift`
evaluates), and the phase is `intCharacter m (p 1) * intCharacter n (p 0)`, the
same phase `Manhattan.V4.type112DStarMixed_parityKernel` carries on the lowering
half. With `intCharacter (-m)`, `intCharacter (-n)` the identity is false: at
`m = n = 0` the two sides differ by `e^{i p₂}`. -/
theorem type12WalshAnalysis_walshRaise_eq {p : Fin 2 → ℝ} {g : ℝ → ℂ}
    (hgper : Function.Periodic g (2 * Real.pi))
    (hg : MemLp g 2 (volume.restrict (Ioc (-Real.pi) Real.pi))) (m n : ℤ) :
    Manhattan.type12WalshAnalysis
        (walshRaise p (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal
          (fourierBasis.repr (rowTorusShift (p 1) (Manhattan.realTorusL2 g hg)))))
        ⟨mixedPairFinset (m, n), isType12Index_mixedPairFinset m n⟩
      = intCharacter m (p 1) * intCharacter n (p 0) *
          mixedFourierCoefficient (fun r _ => Complex.I * (Real.sin r : ℂ) * g r) m n := by
  rw [← mixedFourierCoefficient_raising hgper hg m n]
  refine mixedFourierCoefficient_shift (F := fun r _ : ℝ =>
    Complex.I * (Real.sin r : ℂ) * g r) ?_ ?_ (p 1) (p 0) m n
  · intro beta r
    show Complex.I * (Real.sin (r + 2 * Real.pi) : ℂ) * g (r + 2 * Real.pi)
      = Complex.I * (Real.sin r : ℂ) * g r
    rw [Real.sin_add_two_pi, hgper r]
  · intro _ _; rfl


/-! ## The full degree-two mixed symbol -/

variable {kappa delta : ℝ}

/-- **The degree-two mixed symbol of the Version 4 competitor**, `w - (√2)⁻¹σv`
with `w(r) = i sin(r) g(r)`. Its two halves are the raising half of `D₁f_p` and
`(D₂*k)₁₂`. -/
def v4MixedSymbol (kappa delta : ℝ) (v : ℝ → ℝ → ℝ) (g : ℝ → ℂ) (r beta : ℝ) : ℂ :=
  Complex.I * (Real.sin r : ℂ) * g r - parityMixedSymbol kappa delta v r beta

theorem torusBounded₂_raisingSymbol {g : ℝ → ℂ} (hgmeas : Measurable g) {Kg : ℝ}
    (hgb : ∀ r, ‖g r‖ ≤ Kg) :
    TorusBoundedTwo (fun r _ : ℝ => Complex.I * (Real.sin r : ℂ) * g r) := by
  refine ⟨?_, Kg, fun r _ => ?_⟩
  · exact (measurable_const.mul
      (Complex.measurable_ofReal.comp (Real.measurable_sin.comp measurable_fst))).mul
      (hgmeas.comp measurable_fst)
  · have h1 := Real.abs_sin_le_one r
    have h2 := hgb r
    have hKg : 0 ≤ Kg := le_trans (norm_nonneg _) (hgb 0)
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs]
    nlinarith [abs_nonneg (Real.sin r), norm_nonneg (g r)]

theorem torusBounded₂_v4MixedSymbol (hkappa : 0 < kappa) (hdelta : 0 < delta)
    (v : ParityProfile) {g : ℝ → ℂ} (hgmeas : Measurable g) {Kg : ℝ}
    (hgb : ∀ r, ‖g r‖ ≤ Kg) :
    TorusBoundedTwo (v4MixedSymbol kappa delta v.toFun g) := by
  obtain ⟨hm1, C1, hC1⟩ := torusBounded₂_raisingSymbol hgmeas hgb
  obtain ⟨hm2, C2, hC2⟩ := torusBounded₂_parityMixedSymbol hkappa hdelta v
  exact ⟨hm1.sub hm2, C1 + C2,
    fun r beta => le_trans (norm_sub_le _ _) (add_le_add (hC1 r beta) (hC2 r beta))⟩

theorem torusBounded₂_v4ShiftedSymbol (hkappa : 0 < kappa) (hdelta : 0 < delta)
    (v : ParityProfile) {g : ℝ → ℂ} (hgmeas : Measurable g) {Kg : ℝ}
    (hgb : ∀ r, ‖g r‖ ≤ Kg) (p : Fin 2 → ℝ) :
    TorusBoundedTwo fun s u => v4MixedSymbol kappa delta v.toFun g (p 1 + s) (p 0 + u) :=
  (torusBounded₂_v4MixedSymbol hkappa hdelta v hgmeas hgb).shift (p 1) (p 0)

/-- **The degree-two mixed frequency function of the Version 4 competitor.**
The whole mixed sector vector `D₁f_p - D₂*k_p` is the angle-coordinate `L²`
vector of `w - (√2)⁻¹σv`, read at the shifted frequencies of `(shift)`. -/
theorem type12FreqFun_v4Mixed (hkappa : 0 < kappa) (hdelta : 0 < delta)
    (v : ParityProfile)
    (hvcol : ∀ r, Function.Periodic (fun beta => v.toFun r beta) (2 * Real.pi))
    {g : ℝ → ℂ} (hgmeas : Measurable g) {Kg : ℝ} (hgb : ∀ r, ‖g r‖ ≤ Kg)
    (hgper : Function.Periodic g (2 * Real.pi))
    (hg : MemLp g 2 (volume.restrict (Ioc (-Real.pi) Real.pi))) (p : Fin 2 → ℝ) :
    type12FreqFun
        (Manhattan.type12WalshAnalysis
            (walshRaise p (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal
              (fourierBasis.repr (rowTorusShift (p 1) (Manhattan.realTorusL2 g hg)))))
          - Manhattan.type112DStarMixed p
              (Manhattan.type112ShiftTwist (p 0) (p 1)
                (rawType112Coefficients (torusBounded₃_parityKernel hkappa hdelta v))))
      = mixedAngleL2 (torusBounded₂_v4ShiftedSymbol hkappa hdelta v hgmeas hgb p) := by
  refine type12FreqFun_eq_of_mFourierCoeff _ _ ?_ ?_
  · intro S
    set m := type12RawIndex S 0 with hm
    set n := type12RawIndex S 1 with hn
    have hS : S = ⟨mixedPairFinset (m, n), isType12Index_mixedPairFinset m n⟩ :=
      Subtype.ext (mixedPairFinset_type12RawIndex S).symm
    have hsub : (Manhattan.type12WalshAnalysis
          (walshRaise p (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal
            (fourierBasis.repr (rowTorusShift (p 1) (Manhattan.realTorusL2 g hg)))))
        - Manhattan.type112DStarMixed p
            (Manhattan.type112ShiftTwist (p 0) (p 1)
              (rawType112Coefficients (torusBounded₃_parityKernel hkappa hdelta v)))) S
        = Manhattan.type12WalshAnalysis
            (walshRaise p (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal
              (fourierBasis.repr (rowTorusShift (p 1) (Manhattan.realTorusL2 g hg)))))
            ⟨mixedPairFinset (m, n), isType12Index_mixedPairFinset m n⟩
          - Manhattan.type112DStarMixed p
              (Manhattan.type112ShiftTwist (p 0) (p 1)
                (rawType112Coefficients (torusBounded₃_parityKernel hkappa hdelta v)))
              ⟨mixedPairFinset (m, n), isType12Index_mixedPairFinset m n⟩ := by
      conv_lhs => rw [hS]
      rfl
    rw [mFourierCoeff_mixedAngleL2, hsub,
      ← mixedFourierCoefficient_raising hgper hg m n,
      type112DStarMixed_parityKernel hkappa hdelta v p m n,
      ← mixedFourierCoefficient_shift (parityMixedSymbol_periodic_row v)
        (parityMixedSymbol_periodic_col v hvcol) (p 1) (p 0) m n]
    exact torusIntegral₂_char_sub
      (torusBounded₂_raisingSymbol hgmeas hgb |>.shift (p 1) (p 0))
      ((torusBounded₂_parityMixedSymbol hkappa hdelta v).shift (p 1) (p 0)) m n
  · intro n hn
    obtain ⟨S, hS⟩ := type12RawIndex_surjective n
    exact absurd hS (hn S)


theorem v4MixedSymbol_periodic_row (v : ParityProfile) {g : ℝ → ℂ}
    (hgper : Function.Periodic g (2 * Real.pi)) (beta : ℝ) :
    Function.Periodic (fun r => v4MixedSymbol kappa delta v.toFun g r beta)
      (2 * Real.pi) := by
  intro r
  show v4MixedSymbol kappa delta v.toFun g (r + 2 * Real.pi) beta
    = v4MixedSymbol kappa delta v.toFun g r beta
  have h1 := parityMixedSymbol_periodic_row (kappa := kappa) (delta := delta) v beta r
  simp only at h1
  rw [v4MixedSymbol, v4MixedSymbol, h1, Real.sin_add_two_pi, hgper r]

theorem v4MixedSymbol_periodic_col (v : ParityProfile)
    (hvcol : ∀ r, Function.Periodic (fun beta => v.toFun r beta) (2 * Real.pi))
    (g : ℝ → ℂ) (r : ℝ) :
    Function.Periodic (fun beta => v4MixedSymbol kappa delta v.toFun g r beta)
      (2 * Real.pi) := by
  intro beta
  show v4MixedSymbol kappa delta v.toFun g r (beta + 2 * Real.pi)
    = v4MixedSymbol kappa delta v.toFun g r beta
  have h1 := parityMixedSymbol_periodic_col (kappa := kappa) (delta := delta) v hvcol r beta
  simp only at h1
  rw [v4MixedSymbol, v4MixedSymbol, h1]

/-- **The degree-two dual form of the whole mixed sector**, as an iterated
integral in the shifted frequencies. -/
theorem hMinusEnergy_v4Mixed {q : Estimates.Parameters} (hlam : 0 < q.lambda)
    (hkappa : 0 < kappa) (hdelta : 0 < delta) (v : ParityProfile)
    (hvcol : ∀ r, Function.Periodic (fun beta => v.toFun r beta) (2 * Real.pi))
    {g : ℝ → ℂ} (hgmeas : Measurable g) {Kg : ℝ} (hgb : ∀ r, ‖g r‖ ≤ Kg)
    (hgper : Function.Periodic g (2 * Real.pi))
    (hg : MemLp g 2 (volume.restrict (Ioc (-Real.pi) Real.pi))) (p : Fin 2 → ℝ) :
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hlam
        (Manhattan.type12WalshSynthesis
          (Manhattan.type12WalshAnalysis
              (walshRaise p (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal
                (fourierBasis.repr (rowTorusShift (p 1) (Manhattan.realTorusL2 g hg)))))
            - Manhattan.type112DStarMixed p
                (Manhattan.type112ShiftTwist (p 0) (p 1)
                  (rawType112Coefficients (torusBounded₃_parityKernel hkappa hdelta v)))))
      = Estimates.torusIntegral fun s => Estimates.torusIntegral fun u =>
          Estimates.mixedHMinusWeight q (p 1 + s) (p 0 + u) *
            ‖v4MixedSymbol kappa delta v.toFun g (p 1 + s) (p 0 + u)‖ ^ 2 := by
  obtain ⟨hmeas, M, hM⟩ := torusBounded₂_v4ShiftedSymbol hkappa hdelta v hgmeas hgb p
  refine hMinusEnergy_type12WalshSynthesis_torusIntegral hlam p _
    (fun s u => v4MixedSymbol kappa delta v.toFun g (p 1 + s) (p 0 + u)) hmeas hM ?_
  rw [type12FreqFun_v4Mixed hkappa hdelta v hvcol hgmeas hgb hgper hg p]
  exact coeFn_mixedAngleL2 (torusBounded₂_v4ShiftedSymbol hkappa hdelta v hgmeas hgb p)

/-- **The degree-two residual density of Move 1.** In the unshifted
frequencies the dual energy of the mixed sector is
`∫∫ ‖w - (√2)⁻¹σv‖²/B`. -/
theorem hMinusEnergy_v4Mixed_density {q : Estimates.Parameters} (hlam : 0 < q.lambda)
    (hkappa : 0 < kappa) (hdelta : 0 < delta) (v : ParityProfile)
    (hvcol : ∀ r, Function.Periodic (fun beta => v.toFun r beta) (2 * Real.pi))
    {g : ℝ → ℂ} (hgmeas : Measurable g) {Kg : ℝ} (hgb : ∀ r, ‖g r‖ ≤ Kg)
    (hgper : Function.Periodic g (2 * Real.pi))
    (hg : MemLp g 2 (volume.restrict (Ioc (-Real.pi) Real.pi))) (p : Fin 2 → ℝ) :
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hlam
        (Manhattan.type12WalshSynthesis
          (Manhattan.type12WalshAnalysis
              (walshRaise p (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal
                (fourierBasis.repr (rowTorusShift (p 1) (Manhattan.realTorusL2 g hg)))))
            - Manhattan.type112DStarMixed p
                (Manhattan.type112ShiftTwist (p 0) (p 1)
                  (rawType112Coefficients (torusBounded₃_parityKernel hkappa hdelta v)))))
      = Estimates.torusIntegral fun r => Estimates.torusIntegral fun beta =>
          ‖v4MixedSymbol kappa delta v.toFun g r beta‖ ^ 2
            / Estimates.correctionB q r beta := by
  classical
  rw [hMinusEnergy_v4Mixed hlam hkappa hdelta v hvcol hgmeas hgb hgper hg p]
  set W : ℝ → ℝ → ℝ := fun r beta =>
    Estimates.mixedHMinusWeight q r beta *
      ‖v4MixedSymbol kappa delta v.toFun g r beta‖ ^ 2 with hW
  have hrow : ∀ beta : ℝ, Function.Periodic (fun r => W r beta) (2 * Real.pi) := by
    intro beta r
    have h1 : Estimates.mixedHMinusWeight q (r + 2 * Real.pi) beta
        = Estimates.mixedHMinusWeight q r beta :=
      mixedHMinusWeight_periodic_left q beta r
    have h2 := v4MixedSymbol_periodic_row (kappa := kappa) (delta := delta) v hgper beta r
    simp only at h2
    show W (r + 2 * Real.pi) beta = W r beta
    rw [hW]
    simp only
    rw [h1, h2]
  have hcol : ∀ r : ℝ, Function.Periodic (fun beta => W r beta) (2 * Real.pi) := by
    intro r beta
    have h1 : Estimates.mixedHMinusWeight q r (beta + 2 * Real.pi)
        = Estimates.mixedHMinusWeight q r beta :=
      mixedHMinusWeight_periodic_right q r beta
    have h2 := v4MixedSymbol_periodic_col (kappa := kappa) (delta := delta) v hvcol g r beta
    simp only at h2
    show W r (beta + 2 * Real.pi) = W r beta
    rw [hW]
    simp only
    rw [h1, h2]
  rw [torusIntegral₂_shift hrow hcol (p 1) (p 0)]
  congr 1
  funext r
  congr 1
  funext beta
  show Estimates.mixedHMinusWeight q r beta *
      ‖v4MixedSymbol kappa delta v.toFun g r beta‖ ^ 2 = _
  rw [Estimates.mixedHMinusWeight, Estimates.correctionB, div_eq_mul_inv]
  ring

end Manhattan.V4
