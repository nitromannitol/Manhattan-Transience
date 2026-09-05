import Manhattan.Glue.Transport
import Manhattan.Glue.LoweringClosureBridge
import Manhattan.Glue.DischargeSectors
import Manhattan.Glue.ConcreteRaisingLowDegree
import Manhattan.Glue.Summands
import Manhattan.Estimates.KernelBoundError

/-!
# The degree-two transport, for summand 3 of (22)

Summand 3 of the four-sector form (22) is the squared `H⁻¹` norm of the
degree-two Walsh sector of the residual, `‖D₁f-D₂^*k‖²_{-1}`.  Every
ingredient of Lemma 5.4 that bounds it is already available on the scalar
side (`Manhattan.Estimates.errorHMinusSq_le_rowOrder`,
`Manhattan.Glue.correctionSigmaEnergy_le_sqrtScale`,
`Manhattan.Glue.correctionBEnergy_le_sqrtScale`) and on the coefficient side
(`Manhattan.Glue.type112DStarMixed_eq`, and s
`Manhattan.Glue.lemma_distinct_correction` /
`Manhattan.Glue.lemma_distinct_correction_sigmaEnergy` for the actual
correction, certified by
`Manhattan.Glue.concreteLoweringFormula_correction_certified` -- cite that
PACKAGED theorem, since the bare
`Manhattan.Glue.concreteLoweringFormula_correction` discharges its mixed clause
definitionally and must not be cited alone; the content of that clause is
`Manhattan.Glue.mixedFourierCoefficient_correction`).
`Manhattan.Glue.lemma_distinct_shiftedRawCoefficient` is NOT an ingredient
here: it assumes a diagonal-free kernel, under which `Π₃` acts trivially, so it
is vacuous as a rendering of Lemma 5.3.  What was missing was
the transport that turns a degree-two Walsh vector into the weighted torus
integral those statements are written in.  The docstrings of
`Manhattan/Glue/ScalarIdentification.lean` and
`Manhattan/Glue/FinalDischarge.lean` name exactly the two gaps this file
closes:

* the `H⁻¹` half of the transport in *every* degree
  (`hMinusEnergy_homogeneousWalshSynthesis`).  The
  `Manhattan.Glue.re_inner_coeffH_inv_type112Extend` computes the dual form
  only for a coefficient `d` supplied by hand; `coeffH_bijective` supplies
  it, so the dual energy of any homogeneous Walsh vector is the explicit
  weighted integral of (Hsym).  This is what lets `hMinusEnergy` be computed
  at all, in degree two and in degree four alike;
* the degree-two analogue of `Manhattan.Glue.integral_unitTorus_three`
  (`integral_unitTorus_two`), together with the mixed (type-`12`) sector's
  Fourier transport (`lineIndexFourier_type12Extend`) and the identification
  of its symbol with the paper's mixed `H⁻¹` weight
  (`symbolWeight_type12Pattern`).

The result is `hMinusEnergy_type12WalshSynthesis_torusIntegral`: the dual
energy of a mixed degree-two Walsh vector whose frequency function is a
bounded function of the two line angles is the iterated normalized torus
integral of `Manhattan.Estimates.mixedHMinusWeight` against its squared
modulus, in the manuscript's variables `r = p₂+s` and `β = p₁+u`.

The second half of the file proves Steps 2--4 of Lemma 5.4 on the scalar
(frequency) side, for the explicit correction `k̃` of
`Manhattan.Estimates.correctionCoefficient`:

* `rawD2StarTwoRow_correctionCoefficient` is the first clause of **Step 2**:
  every factor of `k̃` except `sin β` is even in `β`
  (`correctionCoefficient_neg_beta`), so `(D2a)` makes the two-row component
  of `D̃₂*k̃` vanish;
* `rawD2StarMixed_correction_eq` is the second clause of **Step 2**: the mixed component
  `(D̃₂*k̃)_{12}` of `manuscript.tex:1332-1346` is `σ v + U`, with `U` the
  error term `(err)` at a general row frequency (`errorUAt`, which agrees with
  `Manhattan.Estimates.errorU` at `r = -s`);
* `mixedRawResidual_eq` is equation `(onI)`: the mixed residual
  `w - D̃₂*k̃` is `B v - U` everywhere, where `w = 1_I` is the mixed residual
  of `D₁f_p` (Lemma 4.1(c));
* `errorUAt_eq_zero_of_nonneg` is the support statement of Step 2, that `U`
  lives at negative row frequencies;
* `mixedRawResidualHMinusSq_le_energies`,
  `mixedRawResidualHMinusSq_le_reducedIntegral` and
  `mixedRawResidualHMinusSq_le_sqrtScale` are **Steps 3--4**: the squared
  `H⁻¹` norm of `w - D̃₂*k̃` is at most `2∫∫B|v|² + 2‖U‖²_{-1}`, hence at most
  a multiple of the reduced integral `(reduce)` and so at most `C√L`, by
  `Manhattan.Estimates.errorHMinusSq_le_rowOrder` and Proposition 4.2.

The last section carries the first clause of Step 2 to the actual
competitor: `type112DStarTwoRow_correction` shows that the two-row component
of `D₂*k_p` vanishes for the `ℓ²` coefficient `Π₃k̃` of
`Manhattan.correctionType112Coefficients`, at every frozen momentum.  The
route is the `L²` lowering formula (D2a) of
`Manhattan.Glue.type112DStarTwoRow_eq`, which reads the two-row coefficient
off two Walsh coefficients of the input at *column index zero*, together with
`mFourierCoeff_rawCorrection_eq_zero`: `k̃` is odd in `β`, so all its
three-dimensional Fourier coefficients at column index zero vanish.

The last section carries out the *structural* half of summand 3.  The
degree-two Walsh sector of `A_p(f_p+k_p)` has no two-column part
(`inner_verticalPair_walshRaise_axisDegreeOne`,
`inner_verticalPair_concreteFiberA_type112`), so it splits into its two-row
and mixed halves (`walshSectorComponent_two_concreteFiberA_eq`); the two-row
half is `(D₁f_p)₁₁` alone, because `type112DStarTwoRow_correctedLowDegreeData`
kills the competitor's contribution there.  `summandThreeBound_of_sector_bounds`
is the resulting reduction: `SummandThreeBound` follows from one bound on the
two-row sector and one bound on the mixed sector.  Both sectors are given
explicit Walsh coefficients
(`inner_rowPair_walshRaise_axisDegreeOne`,
`type12WalshAnalysis_sub_type112DStarMixed_apply`, the Walsh form of `(onI)`),
and `type11FreqFun_eq_of_mFourierCoeff` /
`type12FreqFun_eq_of_mFourierCoeff` turn the transport hypothesis of
`hMinusEnergy_type12WalshSynthesis_torusIntegral` into a computation of
two-dimensional Fourier coefficients.

What still separates this from `Manhattan.Glue.SummandThreeBound` is exactly
those two Fourier-coefficient computations: the two-row one, whose scalar
input is Lemma 4.1(d), and the mixed one, whose scalar input is
`mixedRawResidualHMinusSq_le_sqrtScale` together with the identification of
the coincident-row term that the concrete `D₂*` drops.

Paper: `manuscript.tex:743-758` ((Hsym)), `manuscript.tex:791-800`
(`eq:shift`), `manuscript.tex:1305-1420` (Lemma 5.4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory UnitAddTorus

namespace Manhattan.Glue

noncomputable section

local instance summandThreePropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-! ### The `H⁻¹` transport in every degree -/

/-- **The dual half of the transport (T).**  The `H⁻¹` energy of a
homogeneous degree-`n` Walsh vector is the weighted integral of (Hsym) with
the reciprocal symbol.  The inverting coefficient is supplied by
`Manhattan.Glue.coeffH_bijective`, so no competitor has to be produced by
hand. -/
theorem hMinusEnergy_homogeneousWalshSynthesis (n : ℕ) {lam : ℝ} (hlam : 0 < lam)
    (p : Fin 2 → ℝ) (c : DegreeCoefficient n) :
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hlam
        (homogeneousWalshSynthesis n c) =
      ∑' σ : Fin n → Axis,
        ∫ t, (symbolWeight n lam p σ t)⁻¹ *
          ‖((lineIndexFourier n c) σ) t‖ ^ 2 ∂(LineTorusMeasure n) := by
  obtain ⟨d, hd⟩ := (coeffH_bijective n hlam p).2 c
  set P := Manhattan.concreteFiberEnvironment.dissipativeSkewPair p with hP
  have hinv : (P.hEquiv hlam).symm (homogeneousWalshSynthesis n c)
      = homogeneousWalshSynthesis n d := by
    rw [ContinuousLinearEquiv.symm_apply_eq]
    show homogeneousWalshSynthesis n c = P.H lam (homogeneousWalshSynthesis n d)
    rw [fiberH_homogeneousWalshSynthesis, hd]
  rw [Manhattan.Operator.DissipativeSkewPair.hMinusEnergy, hinv,
    (homogeneousWalshSynthesis n).inner_map_map,
    ← re_inner_coeffH_inv_eq_integral n hlam p c d hd]
  exact inner_re_symm c d

/-! ### The mixed degree-two Walsh sector as an ordered pair of frequencies -/

theorem mixedPairFinset_isType12 (t : ℤ × ℤ) : IsType12Index (mixedPairFinset t) :=
  isType12Index_mixedPairFinset t.1 t.2

/-- A mixed pair of line coordinates as a genuine mixed Walsh index. -/
def mixedPairIndex (t : ℤ × ℤ) : Type12Index :=
  ⟨mixedPairFinset t, mixedPairFinset_isType12 t⟩

theorem mixedPairIndex_injective : Function.Injective mixedPairIndex := by
  intro s t h
  exact mixedPairFinset_injective (congrArg Subtype.val h)

theorem mixedPairIndex_surjective : Function.Surjective mixedPairIndex := by
  intro T
  obtain ⟨x, y, hxy, hT⟩ := Finset.card_eq_two.mp T.2.1
  have hfil := T.2.2
  rw [hT] at hfil
  rcases x with ⟨ix, k⟩
  rcases y with ⟨iy, l⟩
  cases ix <;> cases iy
  · exfalso
    have hne : (Axis.horizontal, k) ∉ ({(Axis.horizontal, l)} : Finset LineIndex) := by
      simpa using hxy
    rw [Finset.filter_insert, Finset.filter_singleton] at hfil
    simp only [if_true, Finset.card_insert_of_notMem hne] at hfil
    simp at hfil
  · refine ⟨(k, l), Subtype.ext ?_⟩
    change mixedPairFinset (k, l) = T.1
    rw [hT]
    rfl
  · refine ⟨(l, k), Subtype.ext ?_⟩
    change mixedPairFinset (l, k) = T.1
    rw [hT, Finset.pair_comm]
    rfl
  · exfalso
    rw [Finset.filter_insert, Finset.filter_singleton] at hfil
    simp at hfil

@[simp] theorem type12WalshSynthesis_single (S : Type12Index) (a : ℂ) :
    Manhattan.type12WalshSynthesis (lp.single 2 S a) = a • Manhattan.walshL2 S.1 := by
  rw [Manhattan.type12WalshSynthesis, OrthogonalFamily.linearIsometry_apply_single]
  rfl

/-- The canonical identification of mixed pairs of line coordinates with the
mixed Walsh sector. -/
def mixedPairEquiv : (ℤ × ℤ) ≃ Type12Index :=
  Equiv.ofBijective mixedPairIndex
    ⟨mixedPairIndex_injective, mixedPairIndex_surjective⟩

/-- The row and column coordinates carried by a mixed Walsh index. -/
def type12RawIndex (T : Type12Index) : Fin 2 → ℤ :=
  ![(mixedPairEquiv.symm T).1, (mixedPairEquiv.symm T).2]

theorem mixedPairFinset_type12RawIndex (T : Type12Index) :
    mixedPairFinset (type12RawIndex T 0, type12RawIndex T 1) = T.1 := by
  have h := mixedPairEquiv.apply_symm_apply T
  have h1 : mixedPairFinset (mixedPairEquiv.symm T) = T.1 := congrArg Subtype.val h
  simpa [type12RawIndex] using h1

theorem type12RawIndex_injective : Function.Injective type12RawIndex := by
  intro S T h
  have h0 : type12RawIndex S 0 = type12RawIndex T 0 := by rw [h]
  have h1 : type12RawIndex S 1 = type12RawIndex T 1 := by rw [h]
  apply Subtype.ext
  rw [← mixedPairFinset_type12RawIndex S, ← mixedPairFinset_type12RawIndex T, h0, h1]

/-- The degree-two Walsh index underlying a mixed index. -/
def type12Degree (S : Type12Index) : WalshDegreeIndex 2 := ⟨S.1, S.2.1⟩

theorem type12Degree_injective : Function.Injective type12Degree := by
  intro S T h
  exact Subtype.ext (congrArg (fun U : WalshDegreeIndex 2 => U.1) h)

/-- The axis pattern of the sorted enumeration of a mixed index: the
horizontal line first, then the vertical one. -/
def type12Pattern : Fin 2 → Axis := ![Axis.horizontal, Axis.vertical]

section Enumeration

attribute [local instance] lineOrder

/-- The sorted enumeration of a mixed index is the row followed by the
column. -/
theorem degreeEnum_type12Degree (S : Type12Index) :
    degreeEnum (type12Degree S) =
      fun a => (type12Pattern a, type12RawIndex S a) := by
  symm
  apply Finset.orderEmbOfFin_unique
  · intro x
    have hmem : ((type12Pattern x, type12RawIndex S x) : LineIndex) ∈
        mixedPairFinset (type12RawIndex S 0, type12RawIndex S 1) := by
      fin_cases x <;> simp [type12Pattern, mixedPairFinset]
    rwa [mixedPairFinset_type12RawIndex] at hmem
  · rw [Fin.strictMono_iff_lt_succ]
    intro i
    fin_cases i
    show ((Axis.horizontal, type12RawIndex S 0) : LineIndex) <
      (Axis.vertical, type12RawIndex S 1)
    exact horizontal_lt_vertical _ _

end Enumeration

theorem tuplePattern_degreeEnum_type12 (S : Type12Index) :
    tuplePattern (degreeEnum (type12Degree S)) = type12Pattern := by
  rw [degreeEnum_type12Degree]; rfl

theorem tupleCoord_degreeEnum_type12 (S : Type12Index) :
    tupleCoord (degreeEnum (type12Degree S)) = type12RawIndex S := by
  rw [degreeEnum_type12Degree]; rfl

/-! ### The mixed sector inside degree two -/

/-- The constant family of frequency `L²` spaces in degree `n`. -/
abbrev lineFreqFamilyOf (n : ℕ) : (Fin n → Axis) → Type :=
  fun _ => Lp ℂ 2 (LineTorusMeasure n)

/-- `lp.single` in the axis-pattern coordinate, as a linear isometry. -/
def freqSingleOf (n : ℕ) (σ : Fin n → Axis) :
    Lp ℂ 2 (LineTorusMeasure n) →ₗᵢ[ℂ] LineFreqL2 n where
  toLinearMap := lp.lsingle (E := lineFreqFamilyOf n) 2 σ
  norm_map' f := lp.norm_single (E := lineFreqFamilyOf n) two_pos_ennreal σ f

@[simp] theorem freqSingleOf_apply (n : ℕ) (σ : Fin n → Axis)
    (f : Lp ℂ 2 (LineTorusMeasure n)) :
    freqSingleOf n σ f = lp.single (E := lineFreqFamilyOf n) 2 σ f := rfl

/-- Extension by zero from the mixed carrier to degree two. -/
def type12Extend : ℓ²(Type12Index, ℂ) →ₗᵢ[ℂ] DegreeCoefficient 2 :=
  l2Extend type12Degree type12Degree_injective

/-- Extension by zero from the mixed carrier to raw pairs of line
coordinates. -/
def type12RawExtend : ℓ²(Type12Index, ℂ) →ₗᵢ[ℂ] ℓ²(Fin 2 → ℤ, ℂ) :=
  l2Extend type12RawIndex type12RawIndex_injective

/-- The `L²` function of the two line frequencies attached to a mixed
coefficient. -/
def type12FreqFun : ℓ²(Type12Index, ℂ) →ₗᵢ[ℂ] Lp ℂ 2 (LineTorusMeasure 2) :=
  (UnitAddTorus.mFourierBasis (d := Fin 2)).repr.symm.toLinearIsometry.comp
    type12RawExtend

theorem type12FreqFun_single (S : Type12Index) (a : ℂ) :
    type12FreqFun (lp.single 2 S a) = a • mFourierLp 2 (type12RawIndex S) := by
  change (UnitAddTorus.mFourierBasis (d := Fin 2)).repr.symm
      (type12RawExtend (lp.single 2 S a)) = _
  rw [type12RawExtend, l2Extend_single, ← lp_single_smul, map_smul,
    HilbertBasis.repr_symm_single]
  simp

theorem type12WalshSynthesis_eq_homogeneous (c : ℓ²(Type12Index, ℂ)) :
    Manhattan.type12WalshSynthesis c =
      homogeneousWalshSynthesis 2 (type12Extend c) := by
  refine l2_ext' Manhattan.type12WalshSynthesis.toContinuousLinearMap
    ((homogeneousWalshSynthesis 2).toContinuousLinearMap.comp
      type12Extend.toContinuousLinearMap) ?_ c
  intro S
  change Manhattan.type12WalshSynthesis (lp.single 2 S (1 : ℂ)) =
    homogeneousWalshSynthesis 2 (type12Extend (lp.single 2 S (1 : ℂ)))
  rw [type12WalshSynthesis_single, type12Extend, l2Extend_single,
    homogeneousWalshSynthesis_single]
  rfl

/-- Equation (20) for the mixed sector: the line-index Fourier transform of a
mixed degree-two coefficient lives in the single axis sector
`(horizontal, vertical)`. -/
theorem lineIndexFourier_type12Extend (c : ℓ²(Type12Index, ℂ)) :
    lineIndexFourier 2 (type12Extend c) =
      lp.single 2 type12Pattern (type12FreqFun c) := by
  refine l2_ext' ((lineIndexFourier 2).toContinuousLinearMap.comp
      type12Extend.toContinuousLinearMap)
    (((freqSingleOf 2 type12Pattern).comp type12FreqFun).toContinuousLinearMap) ?_ c
  intro S
  change lineIndexFourier 2 (type12Extend (lp.single 2 S (1 : ℂ))) =
    lp.single 2 type12Pattern (type12FreqFun (lp.single 2 S (1 : ℂ)))
  rw [type12Extend, l2Extend_single, lineIndexFourier_single, type12FreqFun_single,
    one_smul, one_smul, orderedFreqFamily, tuplePattern_degreeEnum_type12,
    tupleCoord_degreeEnum_type12]

/-! ### Collapsing the sum over axis patterns -/

theorem integral_weight_zero_gen (n : ℕ)
    (w : (Fin n → Axis) → UnitAddTorus (Fin n) → ℝ) (σ : Fin n → Axis) :
    ∫ t, w σ t * ‖((0 : Lp ℂ 2 (LineTorusMeasure n)) :
        UnitAddTorus (Fin n) → ℂ) t‖ ^ 2 ∂(LineTorusMeasure n) = 0 := by
  rw [show (∫ t, w σ t * ‖((0 : Lp ℂ 2 (LineTorusMeasure n)) :
      UnitAddTorus (Fin n) → ℂ) t‖ ^ 2 ∂(LineTorusMeasure n)) =
      ∫ _t, (0 : ℝ) ∂(LineTorusMeasure n) from ?_, integral_zero]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_zero ℂ 2 (LineTorusMeasure n)] with t ht
  rw [ht]
  simp

/-- A quadratic form supported in a single axis sector. -/
theorem tsum_single_integral_gen (n : ℕ)
    (w : (Fin n → Axis) → UnitAddTorus (Fin n) → ℝ) (σ₀ : Fin n → Axis)
    (F : Lp ℂ 2 (LineTorusMeasure n)) :
    (∑' σ : Fin n → Axis, ∫ t, w σ t *
        ‖((lp.single (E := lineFreqFamilyOf n) 2 σ₀ F : LineFreqL2 n) σ :
          UnitAddTorus (Fin n) → ℂ) t‖ ^ 2 ∂(LineTorusMeasure n)) =
      ∫ t, w σ₀ t *
        ‖(F : UnitAddTorus (Fin n) → ℂ) t‖ ^ 2 ∂(LineTorusMeasure n) := by
  refine tsum_eq_single σ₀ ?_ |>.trans ?_
  · intro σ hσ
    rw [lp.single_apply_ne (E := lineFreqFamilyOf n) 2 σ₀ F hσ]
    exact integral_weight_zero_gen n w σ
  · rw [lp.single_apply_self (E := lineFreqFamilyOf n) 2 σ₀ F]

/-- **The transport (T) for the mixed degree-two sector, `H⁻¹` form.** -/
theorem hMinusEnergy_type12WalshSynthesis {lam : ℝ} (hlam : 0 < lam)
    (p : Fin 2 → ℝ) (c : ℓ²(Type12Index, ℂ)) :
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hlam
        (Manhattan.type12WalshSynthesis c) =
      ∫ t, (symbolWeight 2 lam p type12Pattern t)⁻¹ *
        ‖(type12FreqFun c : UnitAddTorus (Fin 2) → ℂ) t‖ ^ 2
        ∂(LineTorusMeasure 2) := by
  rw [type12WalshSynthesis_eq_homogeneous, hMinusEnergy_homogeneousWalshSynthesis,
    lineIndexFourier_type12Extend]
  exact tsum_single_integral_gen 2 (fun σ t => (symbolWeight 2 lam p σ t)⁻¹)
    type12Pattern (type12FreqFun c)

/-! ### The mixed symbol is the paper's mixed `H⁻¹` weight -/

section Symbol

attribute [local instance] Real.fact_zero_lt_one

theorem totalFrequency_type12_zero (p : Fin 2 → ℝ) (t : UnitAddTorus (Fin 2)) :
    totalFrequency 2 p type12Pattern t 0 = p 0 + 2 * Real.pi * torusLift (t 1) := by
  unfold totalFrequency lineFrequency
  rw [Fin.sum_univ_two]
  simp [lineShiftVector_axisVector, type12Pattern, finAxis]

theorem totalFrequency_type12_one (p : Fin 2 → ℝ) (t : UnitAddTorus (Fin 2)) :
    totalFrequency 2 p type12Pattern t 1 = p 1 + 2 * Real.pi * torusLift (t 0) := by
  unfold totalFrequency lineFrequency
  rw [Fin.sum_univ_two]
  simp [lineShiftVector_axisVector, type12Pattern, finAxis]

/-- The mixed symbol of (Hsym) at the total frequency `(β,r)` of
`manuscript.tex:791-800`: the column line carries `β = p₁+u`, the row line
carries `r = p₂+s`. -/
theorem symbolWeight_type12Pattern (lam : ℝ) (p : Fin 2 → ℝ)
    (t : UnitAddTorus (Fin 2)) :
    symbolWeight 2 lam p type12Pattern t =
      lam + Estimates.dispersion (p 1 + Manhattan.unitTorusAngle (t 0)) +
        Estimates.dispersion (p 0 + Manhattan.unitTorusAngle (t 1)) := by
  obtain ⟨k0, hk0⟩ := two_pi_torusLift (t 0)
  obtain ⟨k1, hk1⟩ := two_pi_torusLift (t 1)
  rw [symbolWeight_def, Estimates.theta]
  have h0 : Estimates.dispersion (totalFrequency 2 p type12Pattern t 0) =
      Estimates.dispersion (p 0 + Manhattan.unitTorusAngle (t 1)) := by
    rw [totalFrequency_type12_zero,
      show p 0 + 2 * Real.pi * torusLift (t 1) =
        (p 0 + Manhattan.unitTorusAngle (t 1)) + k1 * (2 * Real.pi) by rw [hk1]; ring,
      dispersion_add_int_two_pi]
  have h1 : Estimates.dispersion (totalFrequency 2 p type12Pattern t 1) =
      Estimates.dispersion (p 1 + Manhattan.unitTorusAngle (t 0)) := by
    rw [totalFrequency_type12_one,
      show p 1 + 2 * Real.pi * torusLift (t 0) =
        (p 1 + Manhattan.unitTorusAngle (t 0)) + k0 * (2 * Real.pi) by rw [hk0]; ring,
      dispersion_add_int_two_pi]
  rw [h0, h1]
  ring

theorem inv_symbolWeight_type12Pattern (q : Estimates.Parameters) (p : Fin 2 → ℝ)
    (t : UnitAddTorus (Fin 2)) :
    (symbolWeight 2 q.lambda p type12Pattern t)⁻¹ =
      Estimates.mixedHMinusWeight q (p 1 + Manhattan.unitTorusAngle (t 0))
        (p 0 + Manhattan.unitTorusAngle (t 1)) := by
  rw [symbolWeight_type12Pattern, Estimates.mixedHMinusWeight]

end Symbol

/-! ### The degree-two change of variables -/

section ChangeOfVariables

universe u

variable {U : Type u} [MeasureSpace U] [IsProbabilityMeasure (volume : Measure U)]

/-- Iterated integration on a two-fold power of a probability space. -/
theorem integral_pi_two (H : U → U → ℝ)
    (hH : Measurable fun z : U × U => H z.1 z.2)
    {C : ℝ} (hb : ∀ u v, |H u v| ≤ C) :
    (∫ x : Fin 2 → U, H (x 0) (x 1)) = ∫ u, ∫ v, H u v := by
  have step1 : (∫ x : Fin 2 → U, H (x 0) (x 1))
      = ∫ y : U × (Fin 1 → U), H y.1 (y.2 0) :=
    (MeasureTheory.volume_preserving_piFinSuccAbove
      (fun _ : Fin 2 => U) 0).integral_comp'
      (fun y : U × (Fin 1 → U) => H y.1 (y.2 0))
  have hmeas1 : Measurable fun y : U × (Fin 1 → U) => H y.1 (y.2 0) := by
    have hcomp : (fun y : U × (Fin 1 → U) => H y.1 (y.2 0))
        = (fun z : U × U => H z.1 z.2) ∘
          (fun y : U × (Fin 1 → U) => (y.1, y.2 0)) := rfl
    rw [hcomp]
    exact hH.comp (measurable_fst.prodMk
      ((measurable_pi_apply 0).comp measurable_snd))
  have hint1 : Integrable (fun y : U × (Fin 1 → U) => H y.1 (y.2 0))
      (volume.prod volume) :=
    integrable_of_bound hmeas1 (fun _ => hb _ _)
  rw [step1]
  refine Eq.trans (integral_prod _ hint1) ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun uu => ?_)
  have h := (MeasureTheory.measurePreserving_piUnique
    (fun _ : Fin 1 => (volume : Measure U))).integral_comp' (fun v => H uu v)
  simpa using h

end ChangeOfVariables

section TorusTwo

attribute [local instance] Real.fact_zero_lt_one
attribute [local instance] cubicUnitAddCircleMeasureSpace

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- **The degree-two analogue of `Manhattan.Glue.integral_unitTorus_three`.**
A bounded measurable function of the two line angles integrates over the
Fourier torus as the iterated normalized torus integral of the paper. -/
theorem integral_unitTorus_two (F : ℝ → ℝ → ℝ)
    (hF : Measurable fun z : ℝ × ℝ => F z.1 z.2)
    {C : ℝ} (hb : ∀ s u, |F s u| ≤ C) :
    (∫ x : UnitAddTorus (Fin 2),
        F (Manhattan.unitTorusAngle (x 0)) (Manhattan.unitTorusAngle (x 1)))
      = Estimates.torusIntegral fun s => Estimates.torusIntegral fun u => F s u := by
  have hmeasA : Measurable Manhattan.unitTorusAngle :=
    Manhattan.unitTorusAngle_measurable
  have hH : Measurable fun z : UnitAddCircle × UnitAddCircle =>
      F (Manhattan.unitTorusAngle z.1) (Manhattan.unitTorusAngle z.2) :=
    hF.comp ((hmeasA.comp measurable_fst).prodMk (hmeasA.comp measurable_snd))
  rw [integral_pi_two (U := UnitAddCircle)
    (fun x y => F (Manhattan.unitTorusAngle x) (Manhattan.unitTorusAngle y)) hH
    (C := C) (fun _ _ => hb _ _)]
  simp only [integral_unitAddCircle_angle]
  exact integral_unitAddCircle_angle
    (fun s => Estimates.torusIntegral fun u => F s u)

/-- **The mixed degree-two dual energy as the paper's iterated torus
integral.**  If the frequency function of a mixed degree-two Walsh vector is
a bounded function `G` of the row angle `s` and the column angle `u`, then its
squared `H⁻¹` norm is the iterated normalized torus integral of
`Manhattan.Estimates.mixedHMinusWeight` at the shifted frequencies
`r = p₂+s` and `β = p₁+u` against `|G|²`. -/
theorem hMinusEnergy_type12WalshSynthesis_torusIntegral
    {q : Estimates.Parameters} (hlam : 0 < q.lambda) (p : Fin 2 → ℝ)
    (c : ℓ²(Type12Index, ℂ)) (G : ℝ → ℝ → ℂ) {M : ℝ}
    (hGmeas : Measurable fun z : ℝ × ℝ => G z.1 z.2)
    (hGbound : ∀ s u, ‖G s u‖ ≤ M)
    (hG : (type12FreqFun c : UnitAddTorus (Fin 2) → ℂ)
      =ᵐ[LineTorusMeasure 2]
        fun t => G (Manhattan.unitTorusAngle (t 0)) (Manhattan.unitTorusAngle (t 1))) :
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hlam
        (Manhattan.type12WalshSynthesis c) =
      Estimates.torusIntegral fun s => Estimates.torusIntegral fun u =>
        Estimates.mixedHMinusWeight q (p 1 + s) (p 0 + u) * ‖G s u‖ ^ 2 := by
  classical
  set F : ℝ → ℝ → ℝ := fun s u =>
    Estimates.mixedHMinusWeight q (p 1 + s) (p 0 + u) * ‖G s u‖ ^ 2 with hFdef
  have hMnonneg : 0 ≤ M := le_trans (norm_nonneg _) (hGbound 0 0)
  have hweight_pos : ∀ r beta : ℝ, 0 < Estimates.mixedHMinusWeight q r beta := by
    intro r beta
    rw [Estimates.mixedHMinusWeight]
    have h := Estimates.mixed_denominator_pos hlam r beta
    exact inv_pos.mpr h
  have hweight_le : ∀ r beta : ℝ,
      Estimates.mixedHMinusWeight q r beta ≤ q.lambda⁻¹ := by
    intro r beta
    rw [Estimates.mixedHMinusWeight]
    refine (inv_le_inv₀ (Estimates.mixed_denominator_pos hlam r beta) hlam).2 ?_
    linarith [Estimates.dispersion_nonneg r, Estimates.dispersion_nonneg beta]
  have hFbound : ∀ s u : ℝ, |F s u| ≤ q.lambda⁻¹ * M ^ 2 := by
    intro s u
    have h1 : 0 ≤ ‖G s u‖ ^ 2 := sq_nonneg _
    have h2 : ‖G s u‖ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hGbound s u) 2
    have h3 : 0 ≤ F s u :=
      mul_nonneg (hweight_pos (p 1 + s) (p 0 + u)).le h1
    rw [abs_of_nonneg h3, hFdef]
    exact mul_le_mul (hweight_le _ _) h2 h1 (by positivity)
  have hFmeas : Measurable fun z : ℝ × ℝ => F z.1 z.2 := by
    have hw : Measurable fun z : ℝ × ℝ =>
        Estimates.mixedHMinusWeight q (p 1 + z.1) (p 0 + z.2) := by
      unfold Estimates.mixedHMinusWeight Estimates.dispersion
      fun_prop
    exact hw.mul (hGmeas.norm.pow_const 2)
  rw [hMinusEnergy_type12WalshSynthesis hlam p c]
  have hcongr : (∫ t, (symbolWeight 2 q.lambda p type12Pattern t)⁻¹ *
        ‖(type12FreqFun c : UnitAddTorus (Fin 2) → ℂ) t‖ ^ 2
        ∂(LineTorusMeasure 2)) =
      ∫ t, F (Manhattan.unitTorusAngle (t 0)) (Manhattan.unitTorusAngle (t 1))
        ∂(LineTorusMeasure 2) := by
    refine integral_congr_ae ?_
    filter_upwards [hG] with t ht
    rw [ht, inv_symbolWeight_type12Pattern]
  rw [hcongr]
  exact integral_unitTorus_two F hFmeas (C := q.lambda⁻¹ * M ^ 2) hFbound

end TorusTwo

/-! ### The two-row degree-two sector -/

theorem type11RawIndex_injective : Function.Injective type11RawIndex := by
  intro S T h
  have h1 : orderedType11Equiv.symm S = orderedType11Equiv.symm T := Subtype.ext h
  simpa using congrArg orderedType11Equiv h1

/-- The degree-two Walsh index underlying a two-row index. -/
def type11Degree (S : Type11Index) : WalshDegreeIndex 2 := ⟨S.1, S.2.1⟩

theorem type11Degree_injective : Function.Injective type11Degree := by
  intro S T h
  exact Subtype.ext (congrArg (fun U : WalshDegreeIndex 2 => U.1) h)

/-- The axis pattern of the sorted enumeration of a two-row index. -/
def type11Pattern : Fin 2 → Axis := ![Axis.horizontal, Axis.horizontal]

section EnumerationTwoRow

attribute [local instance] lineOrder

theorem degreeEnum_type11Degree (S : Type11Index) :
    degreeEnum (type11Degree S) =
      fun a => (type11Pattern a, type11RawIndex S a) := by
  symm
  apply Finset.orderEmbOfFin_unique
  · intro x
    have hmem : ((type11Pattern x, type11RawIndex S x) : LineIndex) ∈
        rowPairFinset (type11RawIndex S 0, type11RawIndex S 1) := by
      fin_cases x <;> simp [type11Pattern, rowPairFinset]
    rwa [rowPairFinset_type11RawIndex] at hmem
  · rw [Fin.strictMono_iff_lt_succ]
    intro i
    fin_cases i
    show ((Axis.horizontal, type11RawIndex S 0) : LineIndex) <
      (Axis.horizontal, type11RawIndex S 1)
    exact lineIndex_lt_of_coord_lt (type11RawIndex_lt S)

end EnumerationTwoRow

theorem tuplePattern_degreeEnum_type11 (S : Type11Index) :
    tuplePattern (degreeEnum (type11Degree S)) = type11Pattern := by
  rw [degreeEnum_type11Degree]; rfl

theorem tupleCoord_degreeEnum_type11 (S : Type11Index) :
    tupleCoord (degreeEnum (type11Degree S)) = type11RawIndex S := by
  rw [degreeEnum_type11Degree]; rfl

@[simp] theorem type11WalshSynthesis_single (S : Type11Index) (a : ℂ) :
    Manhattan.type11WalshSynthesis (lp.single 2 S a) = a • Manhattan.walshL2 S.1 := by
  rw [Manhattan.type11WalshSynthesis, OrthogonalFamily.linearIsometry_apply_single]
  rfl

/-- Extension by zero from the two-row carrier to degree two. -/
def type11Extend : ℓ²(Type11Index, ℂ) →ₗᵢ[ℂ] DegreeCoefficient 2 :=
  l2Extend type11Degree type11Degree_injective

/-- Extension by zero from the two-row carrier to raw pairs of row
coordinates. -/
def type11RawExtend : ℓ²(Type11Index, ℂ) →ₗᵢ[ℂ] ℓ²(Fin 2 → ℤ, ℂ) :=
  l2Extend type11RawIndex type11RawIndex_injective

/-- The `L²` function of the two row frequencies attached to a two-row
coefficient. -/
def type11FreqFun : ℓ²(Type11Index, ℂ) →ₗᵢ[ℂ] Lp ℂ 2 (LineTorusMeasure 2) :=
  (UnitAddTorus.mFourierBasis (d := Fin 2)).repr.symm.toLinearIsometry.comp
    type11RawExtend

theorem type11FreqFun_single (S : Type11Index) (a : ℂ) :
    type11FreqFun (lp.single 2 S a) = a • mFourierLp 2 (type11RawIndex S) := by
  change (UnitAddTorus.mFourierBasis (d := Fin 2)).repr.symm
      (type11RawExtend (lp.single 2 S a)) = _
  rw [type11RawExtend, l2Extend_single, ← lp_single_smul, map_smul,
    HilbertBasis.repr_symm_single]
  simp

theorem type11WalshSynthesis_eq_homogeneous (c : ℓ²(Type11Index, ℂ)) :
    Manhattan.type11WalshSynthesis c =
      homogeneousWalshSynthesis 2 (type11Extend c) := by
  refine l2_ext' Manhattan.type11WalshSynthesis.toContinuousLinearMap
    ((homogeneousWalshSynthesis 2).toContinuousLinearMap.comp
      type11Extend.toContinuousLinearMap) ?_ c
  intro S
  change Manhattan.type11WalshSynthesis (lp.single 2 S (1 : ℂ)) =
    homogeneousWalshSynthesis 2 (type11Extend (lp.single 2 S (1 : ℂ)))
  rw [type11WalshSynthesis_single, type11Extend, l2Extend_single,
    homogeneousWalshSynthesis_single]
  rfl

/-- Equation (20) for the two-row sector. -/
theorem lineIndexFourier_type11Extend (c : ℓ²(Type11Index, ℂ)) :
    lineIndexFourier 2 (type11Extend c) =
      lp.single 2 type11Pattern (type11FreqFun c) := by
  refine l2_ext' ((lineIndexFourier 2).toContinuousLinearMap.comp
      type11Extend.toContinuousLinearMap)
    (((freqSingleOf 2 type11Pattern).comp type11FreqFun).toContinuousLinearMap) ?_ c
  intro S
  change lineIndexFourier 2 (type11Extend (lp.single 2 S (1 : ℂ))) =
    lp.single 2 type11Pattern (type11FreqFun (lp.single 2 S (1 : ℂ)))
  rw [type11Extend, l2Extend_single, lineIndexFourier_single, type11FreqFun_single,
    one_smul, one_smul, orderedFreqFamily, tuplePattern_degreeEnum_type11,
    tupleCoord_degreeEnum_type11]

/-- **The transport (T) for the two-row degree-two sector, `H⁻¹` form.** -/
theorem hMinusEnergy_type11WalshSynthesis {lam : ℝ} (hlam : 0 < lam)
    (p : Fin 2 → ℝ) (c : ℓ²(Type11Index, ℂ)) :
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hlam
        (Manhattan.type11WalshSynthesis c) =
      ∫ t, (symbolWeight 2 lam p type11Pattern t)⁻¹ *
        ‖(type11FreqFun c : UnitAddTorus (Fin 2) → ℂ) t‖ ^ 2
        ∂(LineTorusMeasure 2) := by
  rw [type11WalshSynthesis_eq_homogeneous, hMinusEnergy_homogeneousWalshSynthesis,
    lineIndexFourier_type11Extend]
  exact tsum_single_integral_gen 2 (fun σ t => (symbolWeight 2 lam p σ t)⁻¹)
    type11Pattern (type11FreqFun c)

section SymbolTwoRow

attribute [local instance] Real.fact_zero_lt_one

theorem totalFrequency_type11_zero (p : Fin 2 → ℝ) (t : UnitAddTorus (Fin 2)) :
    totalFrequency 2 p type11Pattern t 0 = p 0 := by
  unfold totalFrequency lineFrequency
  rw [Fin.sum_univ_two]
  simp [lineShiftVector_axisVector, type11Pattern, finAxis]

theorem totalFrequency_type11_one (p : Fin 2 → ℝ) (t : UnitAddTorus (Fin 2)) :
    totalFrequency 2 p type11Pattern t 1 =
      p 1 + 2 * Real.pi * (torusLift (t 0) + torusLift (t 1)) := by
  unfold totalFrequency lineFrequency
  rw [Fin.sum_univ_two]
  simp [lineShiftVector_axisVector, type11Pattern, finAxis]

/-- The two-row symbol of (Hsym): the first coordinate of the total frequency
stays at `p₁`, the second is the sum of the two shifted row frequencies. -/
theorem symbolWeight_type11Pattern (lam : ℝ) (p : Fin 2 → ℝ)
    (t : UnitAddTorus (Fin 2)) :
    symbolWeight 2 lam p type11Pattern t =
      lam + Estimates.dispersion (p 0) +
        Estimates.dispersion (p 1 + Manhattan.unitTorusAngle (t 0) +
          Manhattan.unitTorusAngle (t 1)) := by
  obtain ⟨k0, hk0⟩ := two_pi_torusLift (t 0)
  obtain ⟨k1, hk1⟩ := two_pi_torusLift (t 1)
  rw [symbolWeight_def, Estimates.theta, totalFrequency_type11_zero]
  have h1 : Estimates.dispersion (totalFrequency 2 p type11Pattern t 1) =
      Estimates.dispersion (p 1 + Manhattan.unitTorusAngle (t 0) +
        Manhattan.unitTorusAngle (t 1)) := by
    rw [totalFrequency_type11_one,
      show p 1 + 2 * Real.pi * (torusLift (t 0) + torusLift (t 1)) =
        (p 1 + Manhattan.unitTorusAngle (t 0) + Manhattan.unitTorusAngle (t 1)) +
          ((k0 + k1 : ℤ) : ℝ) * (2 * Real.pi) by
        rw [show 2 * Real.pi * (torusLift (t 0) + torusLift (t 1)) =
          2 * Real.pi * torusLift (t 0) + 2 * Real.pi * torusLift (t 1) by ring,
          hk0, hk1]
        push_cast
        ring,
      dispersion_add_int_two_pi]
  rw [h1]
  ring

theorem inv_symbolWeight_type11Pattern (q : Estimates.Parameters) (p : Fin 2 → ℝ)
    (t : UnitAddTorus (Fin 2)) :
    (symbolWeight 2 q.lambda p type11Pattern t)⁻¹ =
      Estimates.twoRowHMinusWeight q (p 0)
        (p 1 + Manhattan.unitTorusAngle (t 0) + Manhattan.unitTorusAngle (t 1)) := by
  rw [symbolWeight_type11Pattern, Estimates.twoRowHMinusWeight]

end SymbolTwoRow

/-! ### The degree-two sector of an arbitrary Walsh vector -/

/-- The degree-`n` Walsh sector component is the homogeneous synthesis of the
degree-`n` analysis. -/
theorem walshSectorComponent_eq_homogeneous (n : ℕ) (x : WalshL2) :
    walshSectorComponent (fun S => S.card = n) x =
      homogeneousWalshSynthesis n (Manhattan.walshSectorAnalysis
        (fun S : Finset LineIndex => S.card = n) x) := rfl

/-- **The dual energy of a Walsh degree sector.**  This is the form in which
summands 3 and 4 of (22) are stated: the squared `H⁻¹` norm of the degree-`n`
component of a residual is the weighted integral of (Hsym) with reciprocal
symbol, taken on the line-frequency transform of its degree-`n` Walsh
coefficients.
-/
theorem hMinusEnergy_walshSectorComponent (n : ℕ) {lam : ℝ} (hlam : 0 < lam)
    (p : Fin 2 → ℝ) (x : WalshL2) :
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hlam
        (walshSectorComponent (fun S => S.card = n) x) =
      ∑' σ : Fin n → Axis,
        ∫ t, (symbolWeight n lam p σ t)⁻¹ *
          ‖((lineIndexFourier n (Manhattan.walshSectorAnalysis
              (fun S : Finset LineIndex => S.card = n) x)) σ) t‖ ^ 2
          ∂(LineTorusMeasure n) := by
  rw [walshSectorComponent_eq_homogeneous, hMinusEnergy_homogeneousWalshSynthesis]

/-! ## Steps 2--4 of Lemma 5.4, on the scalar (frequency) side -/

section ScalarStepTwo

open Manhattan.Estimates Set

/-- The scalar integrand of (D2b) applied to the explicit correction. -/
def mixedRawIntegrand (q : Parameters) (a p₂ r r' beta : ℝ) : ℝ :=
  (multiplier 40 q (mixedTotalFrequency beta (r + r' - p₂)))⁻¹ *
    (correctionV 40 q a r beta *
        (if r + r' - p₂ ∈ correctionInterval q a r beta then 1 else 0) +
      correctionV 40 q a r' beta *
        (if r + r' - p₂ ∈ correctionInterval q a r' beta then 1 else 0))

theorem correctionCoefficient_eq_ofReal (q : Parameters) (a p₂ r r' beta : ℝ) :
    correctionCoefficient 40 q a p₂ r r' beta =
      Complex.I * (Real.sin beta : ℂ) *
        ((mixedRawIntegrand q a p₂ r r' beta : ℝ) : ℂ) := by
  simp only [correctionCoefficient, mixedRawIntegrand]
  push_cast
  split_ifs <;> push_cast <;> ring

/-- The error term `U` of `(err)` at a general row frequency `r`. -/
def errorUAt (q : Parameters) (a p₂ r beta : ℝ) : ℝ :=
  Real.sin beta ^ 2 * torusIntegral (fun t : ℝ =>
    if r + t - p₂ ∈ correctionInterval q a t beta then
      correctionV 40 q a t beta *
        (multiplier 40 q (mixedTotalFrequency beta (r + t - p₂)))⁻¹
    else 0)

theorem errorUAt_neg (q : Parameters) (a p₂ s beta : ℝ) :
    errorUAt q a p₂ (-s) beta = errorU q a p₂ s beta := rfl

/-- The `(D2b)` mixed component of the raw correction is a real function. -/
theorem rawD2StarMixed_correctionCoefficient (q : Parameters) (a p₂ r beta : ℝ) :
    rawD2StarMixed (correctionCoefficient 40 q a p₂) r beta =
      ((Real.sin beta ^ 2 *
        torusIntegral (fun r' => mixedRawIntegrand q a p₂ r r' beta) : ℝ) : ℂ) := by
  have hpt : (fun r' => correctionCoefficient 40 q a p₂ r r' beta) =
      fun r' => (Complex.I * (Real.sin beta : ℂ)) *
        ((mixedRawIntegrand q a p₂ r r' beta : ℝ) : ℂ) := by
    funext r'
    rw [correctionCoefficient_eq_ofReal]
  rw [rawD2StarMixed, hpt, torusIntegral_const_mul]
  have hre : torusIntegral (fun r' => ((mixedRawIntegrand q a p₂ r r' beta : ℝ) : ℂ)) =
      ((torusIntegral (fun r' => mixedRawIntegrand q a p₂ r r' beta) : ℝ) : ℂ) := by
    rw [torusIntegral, torusIntegral, integral_complex_ofReal]
    simp [Complex.real_smul]
  rw [hre]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-! ### Splitting (D2b) into the diagonal summand and the error -/

/-- The diagonal summand of the (D2b) integrand. -/
def mixedRawSelfIntegrand (q : Parameters) (a p₂ r r' beta : ℝ) : ℝ :=
  correctionV 40 q a r beta *
    (if r + r' - p₂ ∈ correctionInterval q a r beta then
      (multiplier 40 q (mixedTotalFrequency beta (r + r' - p₂)))⁻¹ else 0)

/-- The error summand of the (D2b) integrand. -/
def mixedRawErrorIntegrand (q : Parameters) (a p₂ r r' beta : ℝ) : ℝ :=
  if r + r' - p₂ ∈ correctionInterval q a r' beta then
    correctionV 40 q a r' beta *
      (multiplier 40 q (mixedTotalFrequency beta (r + r' - p₂)))⁻¹
  else 0

theorem mixedRawIntegrand_eq (q : Parameters) (a p₂ r r' beta : ℝ) :
    mixedRawIntegrand q a p₂ r r' beta =
      mixedRawSelfIntegrand q a p₂ r r' beta +
        mixedRawErrorIntegrand q a p₂ r r' beta := by
  unfold mixedRawIntegrand mixedRawSelfIntegrand mixedRawErrorIntegrand
  split_ifs <;> ring

theorem measurableSet_correctionInterval (q : Parameters) (a r beta : ℝ) :
    MeasurableSet (correctionInterval q a r beta) := by
  unfold correctionInterval
  split_ifs
  · exact measurableSet_Icc
  · exact MeasurableSet.empty

theorem measurable_inv_multiplier_comp (q : Parameters) (beta : ℝ) {g : ℝ → ℝ}
    (hg : Measurable g) :
    Measurable fun r' : ℝ =>
      (multiplier 40 q (mixedTotalFrequency beta (g r')))⁻¹ := by
  unfold multiplier theta mixedTotalFrequency dispersion
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  fun_prop

theorem multiplier_ge_lambda {q : Parameters} (P : Fin 2 → ℝ) :
    40 * q.lambda ≤ multiplier 40 q P := by
  unfold multiplier
  have h := theta_nonneg P
  nlinarith [abs_nonneg (Real.sin (P 0 / 2)), abs_nonneg (Real.sin (P 1 / 2))]

theorem inv_multiplier_le {q : Parameters} (hlam : 0 < q.lambda) (P : Fin 2 → ℝ) :
    (multiplier 40 q P)⁻¹ ≤ (40 * q.lambda)⁻¹ :=
  inv_anti₀ (by positivity) (multiplier_ge_lambda P)

theorem inv_multiplier_nonneg {q : Parameters} (hlam : 0 < q.lambda)
    (P : Fin 2 → ℝ) : 0 ≤ (multiplier 40 q P)⁻¹ :=
  inv_nonneg.2 (multiplier_nonneg (by norm_num) hlam.le P)

theorem measurable_mixedShift (r p₂ : ℝ) :
    Measurable fun r' : ℝ => r + r' - p₂ :=
  (measurable_const.add measurable_id).sub_const p₂

theorem mixedRawSelfIntegrand_integrable {q : Parameters} (hq : q.Admissible)
    (a p₂ r beta : ℝ) :
    Integrable (fun r' => mixedRawSelfIntegrand q a p₂ r r' beta)
      (volume.restrict torus) := by
  have hlam : 0 < q.lambda := hq.1
  have hset : MeasurableSet {r' : ℝ | r + r' - p₂ ∈ correctionInterval q a r beta} :=
    (measurable_mixedShift r p₂) (measurableSet_correctionInterval q a r beta)
  have hval : Measurable fun r' : ℝ =>
      (multiplier 40 q (mixedTotalFrequency beta (r + r' - p₂)))⁻¹ :=
    measurable_inv_multiplier_comp q beta (measurable_mixedShift r p₂)
  refine integrableOn_torus_of_bounded (C := q.lambda⁻¹ * (40 * q.lambda)⁻¹) ?_ ?_
  · unfold mixedRawSelfIntegrand
    exact measurable_const.mul (Measurable.ite hset hval measurable_const)
  · intro r'
    unfold mixedRawSelfIntegrand
    have hv0 := correctionV_nonneg hq a r beta
    have hv := correctionV_le_inv hq a r beta
    have hmul : |(if r + r' - p₂ ∈ correctionInterval q a r beta then
        (multiplier 40 q (mixedTotalFrequency beta (r + r' - p₂)))⁻¹ else 0)| ≤
          (40 * q.lambda)⁻¹ := by
      split_ifs with h
      · rw [abs_of_nonneg (inv_multiplier_nonneg hlam _)]
        exact inv_multiplier_le hlam _
      · rw [abs_zero]; positivity
    rw [abs_mul, abs_of_nonneg hv0]
    exact mul_le_mul hv hmul (abs_nonneg _) (by positivity)

theorem mixedRawErrorIntegrand_integrable {q : Parameters} (hq : q.Admissible)
    (a p₂ r beta : ℝ) :
    Integrable (fun r' => mixedRawErrorIntegrand q a p₂ r r' beta)
      (volume.restrict torus) := by
  have hlam : 0 < q.lambda := hq.1
  have hset : MeasurableSet {r' : ℝ | r + r' - p₂ ∈ correctionInterval q a r' beta} := by
    have := measurableSet_errorSupport q a p₂ (-r) beta
    simpa using this
  have hval : Measurable fun r' : ℝ =>
      (multiplier 40 q (mixedTotalFrequency beta (r + r' - p₂)))⁻¹ :=
    measurable_inv_multiplier_comp q beta (measurable_mixedShift r p₂)
  refine integrableOn_torus_of_bounded (C := q.lambda⁻¹ * (40 * q.lambda)⁻¹) ?_ ?_
  · unfold mixedRawErrorIntegrand
    exact Measurable.ite hset
      ((correctionV_measurable_left 40 q a beta).mul hval) measurable_const
  · intro r'
    unfold mixedRawErrorIntegrand
    split_ifs with h
    · rw [abs_mul, abs_of_nonneg (correctionV_nonneg hq a r' beta),
        abs_of_nonneg (inv_multiplier_nonneg hlam _)]
      exact mul_le_mul (correctionV_le_inv hq a r' beta)
        (inv_multiplier_le hlam _) (inv_multiplier_nonneg hlam _) (by positivity)
    · rw [abs_zero]; positivity

/-! ### Step 2 of Lemma 5.4 -/

theorem correctionInterval_subset_Icc {q : Parameters} (hq : q.Admissible)
    {a : ℝ} (ha : 0 ≤ a) (r beta : ℝ) :
    correctionInterval q a r beta ⊆ Icc (-q.rho) 0 := by
  unfold correctionInterval
  split_ifs with h
  · obtain ⟨hr, _⟩ := h
    rw [Parameters.supportInterval, mem_Icc] at hr
    have hK : (20:ℝ) ≤ q.K := hq.2.2.1
    have hdelta : 0 ≤ q.delta a := by
      rw [Parameters.delta]; positivity
    have hrpos : 0 ≤ r := le_trans (by positivity) hr.1
    intro s hs
    rw [mem_Icc] at hs ⊢
    refine ⟨hs.1, le_trans hs.2 ?_⟩
    have : 0 ≤ q.K * (r + q.delta a + |beta|) := by positivity
    linarith
  · exact fun s hs => absurd hs (notMem_empty s)

theorem torusIntegral_mixedRawIntegrand_split {q : Parameters} (hq : q.Admissible)
    (a p₂ r beta : ℝ) :
    torusIntegral (fun r' => mixedRawIntegrand q a p₂ r r' beta) =
      torusIntegral (fun r' => mixedRawSelfIntegrand q a p₂ r r' beta) +
        torusIntegral (fun r' => mixedRawErrorIntegrand q a p₂ r r' beta) := by
  simp only [mixedRawIntegrand_eq]
  exact cubicTorusIntegral_add (mixedRawSelfIntegrand_integrable hq a p₂ r beta)
    (mixedRawErrorIntegrand_integrable hq a p₂ r beta)

theorem sin_sq_torusIntegral_error (q : Parameters) (a p₂ r beta : ℝ) :
    Real.sin beta ^ 2 *
        torusIntegral (fun r' => mixedRawErrorIntegrand q a p₂ r r' beta) =
      errorUAt q a p₂ r beta := rfl

theorem sin_sq_torusIntegral_self {q : Parameters} (hq : q.Admissible)
    {a p₂ : ℝ} (ha : 0 ≤ a) (hp₂ : |p₂| ≤ a) (r beta : ℝ) :
    Real.sin beta ^ 2 *
        torusIntegral (fun r' => mixedRawSelfIntegrand q a p₂ r r' beta) =
      correctionSigma 40 q a r beta * correctionV 40 q a r beta := by
  set hfun : ℝ → ℝ := fun s =>
    if s ∈ correctionInterval q a r beta then
      (multiplier 40 q (mixedTotalFrequency beta s))⁻¹ else 0 with hfundef
  have hshift : (fun r' => mixedRawSelfIntegrand q a p₂ r r' beta) =
      fun r' => correctionV 40 q a r beta * hfun (r - p₂ + r') := by
    funext r'
    rw [mixedRawSelfIntegrand, hfundef]
    simp only
    rw [show r - p₂ + r' = r + r' - p₂ by ring]
  rw [hshift, torusIntegral_smul_left]
  by_cases hr : r ∈ q.supportInterval a
  · have hK : (20:ℝ) ≤ q.K := hq.2.2.1
    have hrho : 0 < q.rho := hq.2.2.2.1
    have hrhopi : q.rho ≤ Real.pi / 20 := hq.2.2.2.2
    have hpi : 3 * q.rho < Real.pi := by
      have := Real.pi_pos; linarith
    have hdelta : 0 ≤ q.delta a := by rw [Parameters.delta]; positivity
    have hrmem := hr
    rw [Parameters.supportInterval, mem_Icc] at hrmem
    have hp₂le : |p₂| ≤ q.delta a := by
      refine le_trans hp₂ ?_
      rw [Parameters.delta]
      have := Real.sqrt_nonneg q.lambda; linarith
    have hp₂bounds := abs_le.mp hp₂le
    have hKdelta : q.K * q.delta a ≤ r := hrmem.1
    have hdeltaK : 20 * q.delta a ≤ r := by nlinarith
    have hr0 : r ≤ q.r0 := hrmem.2
    have hr0def : q.r0 = q.rho / (100 * q.K) := rfl
    have hKpos : (0:ℝ) < q.K := by linarith
    have hr0le : 100 * q.K * q.r0 = q.rho := by
      rw [hr0def]; field_simp
    have hc : |r - p₂| ≤ q.rho := by
      rw [abs_le]
      constructor
      · nlinarith [hp₂bounds.1, hp₂bounds.2]
      · nlinarith [hp₂bounds.1, hp₂bounds.2]
    have hsupp : ∀ s, s ∉ Icc (-q.rho) 0 → hfun s = 0 := by
      intro s hs
      rw [hfundef]
      simp only
      rw [if_neg]
      intro hmem
      exact hs (correctionInterval_subset_Icc hq ha r beta hmem)
    rw [torusIntegral_translate hpi hc hsupp]
    rw [correctionSigma]
    ring
  · have hv : correctionV 40 q a r beta = 0 := by
      rw [correctionV, if_neg hr]
    rw [hv]
    ring

/-- **Step 2 of Lemma 5.4.**  The mixed component of `D̃₂*k̃` is `σ v + U`. -/
theorem rawD2StarMixed_correction_eq {q : Parameters} (hq : q.Admissible)
    {a p₂ : ℝ} (ha : 0 ≤ a) (hp₂ : |p₂| ≤ a) (r beta : ℝ) :
    rawD2StarMixed (correctionCoefficient 40 q a p₂) r beta =
      ((correctionSigma 40 q a r beta * correctionV 40 q a r beta +
        errorUAt q a p₂ r beta : ℝ) : ℂ) := by
  rw [rawD2StarMixed_correctionCoefficient,
    torusIntegral_mixedRawIntegrand_split hq, mul_add,
    sin_sq_torusIntegral_self hq ha hp₂, sin_sq_torusIntegral_error]

/-! ### Iterated torus integrals of bounded measurable functions -/

theorem measurable_torusIntegral_left {g : ℝ → ℝ → ℝ}
    (hg : Measurable fun z : ℝ × ℝ => g z.1 z.2) :
    Measurable fun x => torusIntegral fun y => g x y := by
  unfold torusIntegral
  simp only [smul_eq_mul]
  exact hg.stronglyMeasurable.integral_prod_right.measurable.const_mul _

theorem torusIntegral₂_mono {f g : ℝ → ℝ → ℝ}
    (hgm : Measurable fun z : ℝ × ℝ => g z.1 z.2) {C : ℝ}
    (hgb : ∀ x y, |g x y| ≤ C)
    (hf : ∀ x y, 0 ≤ f x y) (hfg : ∀ x y, f x y ≤ g x y) :
    (torusIntegral fun x => torusIntegral fun y => f x y) ≤
      torusIntegral fun x => torusIntegral fun y => g x y := by
  refine torusIntegral_mono' (fun x => torusIntegral_nonneg' (fun y => hf x y)) ?_ ?_
  · exact integrableOn_torus_of_bounded (measurable_torusIntegral_left hgm)
      (fun x => abs_torusIntegral_le (hgb x))
  · intro x
    exact torusIntegral_mono' (hf x)
      (integrableOn_torus_of_bounded (hgm.comp measurable_prodMk_left) (hgb x))
      (hfg x)

theorem torusIntegral₂_add {f g : ℝ → ℝ → ℝ}
    (hfm : Measurable fun z : ℝ × ℝ => f z.1 z.2) {C : ℝ}
    (hfb : ∀ x y, |f x y| ≤ C)
    (hgm : Measurable fun z : ℝ × ℝ => g z.1 z.2) {D : ℝ}
    (hgb : ∀ x y, |g x y| ≤ D) :
    (torusIntegral fun x => torusIntegral fun y => (f x y + g x y)) =
      (torusIntegral fun x => torusIntegral fun y => f x y) +
        torusIntegral fun x => torusIntegral fun y => g x y := by
  have hinner : ∀ x, (torusIntegral fun y => (f x y + g x y)) =
      (torusIntegral fun y => f x y) + torusIntegral fun y => g x y := by
    intro x
    exact cubicTorusIntegral_add
      (integrableOn_torus_of_bounded (hfm.comp measurable_prodMk_left) (hfb x))
      (integrableOn_torus_of_bounded (hgm.comp measurable_prodMk_left) (hgb x))
  simp only [hinner]
  exact cubicTorusIntegral_add
    (integrableOn_torus_of_bounded (measurable_torusIntegral_left hfm)
      (fun x => abs_torusIntegral_le (hfb x)))
    (integrableOn_torus_of_bounded (measurable_torusIntegral_left hgm)
      (fun x => abs_torusIntegral_le (hgb x)))

theorem torusIntegral₂_swap {f : ℝ → ℝ → ℝ}
    (hfm : Measurable fun z : ℝ × ℝ => f z.1 z.2) {C : ℝ}
    (hfb : ∀ x y, |f x y| ≤ C) :
    (torusIntegral fun x => torusIntegral fun y => f x y) =
      torusIntegral fun y => torusIntegral fun x => f x y := by
  refine cubicTorusIntegral_swap f ?_
  refine Integrable.mono' (integrable_const C) ?_ ?_
  · exact hfm.aestronglyMeasurable
  · filter_upwards with z
    simpa [Real.norm_eq_abs] using hfb z.1 z.2

/-- Reflection invariance of the normalized torus integral. -/
theorem torusIntegral_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (g : ℝ → E) :
    (torusIntegral fun s => g (-s)) = torusIntegral g := by
  have hpi : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  unfold torusIntegral torus
  congr 1
  rw [← intervalIntegral.integral_of_le hpi, ← intervalIntegral.integral_of_le hpi,
    intervalIntegral.integral_comp_neg]
  simp

/-! ### The error is supported at negative row frequencies -/

theorem errorUAt_eq_zero_of_nonneg {q : Parameters} (hq : q.Admissible)
    {a p₂ r : ℝ} (ha : 0 ≤ a) (hp₂ : |p₂| ≤ a) (hr : 0 ≤ r) (beta : ℝ) :
    errorUAt q a p₂ r beta = 0 := by
  have hdelta : 0 < q.delta a := delta_pos hq ha
  have hK : (20:ℝ) ≤ q.K := hq.2.2.1
  have hp₂delta : |p₂| ≤ q.delta a := by
    refine le_trans hp₂ ?_
    rw [Parameters.delta]
    have := Real.sqrt_nonneg q.lambda; linarith
  have hp₂bounds := abs_le.mp hp₂delta
  have hzero : ∀ t : ℝ, (if r + t - p₂ ∈ correctionInterval q a t beta then
      correctionV 40 q a t beta *
        (multiplier 40 q (mixedTotalFrequency beta (r + t - p₂)))⁻¹
      else 0) = 0 := by
    intro t
    rw [if_neg]
    intro hmem
    unfold correctionInterval at hmem
    split_ifs at hmem with hcond
    · obtain ⟨ht, _⟩ := hcond
      rw [Parameters.supportInterval, mem_Icc] at ht
      rw [mem_Icc] at hmem
      have htpos : 0 ≤ t := le_trans (by positivity) ht.1
      have hKt : q.K * q.delta a ≤ t := ht.1
      have habs : 0 ≤ |beta| := abs_nonneg beta
      nlinarith [hmem.2, hp₂bounds.2]
    · exact absurd hmem (notMem_empty _)
  unfold errorUAt
  simp only [hzero]
  simp [torusIntegral]

/-! ### The mixed raw residual `w - D̃₂*k̃` -/

/-- The paper's `w(r,β)=1_I(r)`, the mixed component of `D₁f_p`. -/
def rawMixedTarget (q : Parameters) (a r : ℝ) : ℝ :=
  if r ∈ q.supportInterval a then 1 else 0

/-- The mixed residual `w - D̃₂*k̃` of Lemma 5.4. -/
def mixedRawResidual (q : Parameters) (a p₂ r beta : ℝ) : ℂ :=
  ((rawMixedTarget q a r : ℝ) : ℂ) -
    rawD2StarMixed (correctionCoefficient 40 q a p₂) r beta

/-- **Equation (onI).**  The mixed residual is `Bv - U`. -/
theorem mixedRawResidual_eq {q : Parameters} (hq : q.Admissible)
    {a p₂ : ℝ} (ha : 0 ≤ a) (hp₂ : |p₂| ≤ a) (r beta : ℝ) :
    mixedRawResidual q a p₂ r beta =
      ((correctionB q r beta * correctionV 40 q a r beta -
        errorUAt q a p₂ r beta : ℝ) : ℂ) := by
  rw [mixedRawResidual, rawD2StarMixed_correction_eq hq ha hp₂]
  push_cast
  rw [rawMixedTarget]
  by_cases hr : r ∈ q.supportInterval a
  · rw [if_pos hr]
    have hne : correctionB q r beta + correctionSigma 40 q a r beta ≠ 0 :=
      ne_of_gt (correctionDenominator_pos (by norm_num) hq.1 a r beta)
    have h := one_sub_sigma_mul_correctionV (kappa := 40) hr hne
    push_cast
    rw [show ((1:ℂ) - (↑(correctionSigma 40 q a r beta) *
        ↑(correctionV 40 q a r beta) + ↑(errorUAt q a p₂ r beta))) =
      ((1 - correctionSigma 40 q a r beta * correctionV 40 q a r beta : ℝ) : ℂ) -
        ((errorUAt q a p₂ r beta : ℝ) : ℂ) by push_cast; ring, h]
    push_cast
    ring
  · rw [if_neg hr]
    have hv : correctionV 40 q a r beta = 0 := by rw [correctionV, if_neg hr]
    rw [hv]
    push_cast
    ring

/-! ### Uniform bounds and joint measurability -/

theorem mixedRawErrorIntegrand_abs_le {q : Parameters} (hq : q.Admissible)
    (a p₂ r r' beta : ℝ) :
    |mixedRawErrorIntegrand q a p₂ r r' beta| ≤ q.lambda⁻¹ * (40 * q.lambda)⁻¹ := by
  have hlam : 0 < q.lambda := hq.1
  unfold mixedRawErrorIntegrand
  split_ifs with h
  · rw [abs_mul, abs_of_nonneg (correctionV_nonneg hq a r' beta),
      abs_of_nonneg (inv_multiplier_nonneg hlam _)]
    exact mul_le_mul (correctionV_le_inv hq a r' beta)
      (inv_multiplier_le hlam _) (inv_multiplier_nonneg hlam _) (by positivity)
  · rw [abs_zero]; positivity

theorem errorUAt_abs_le {q : Parameters} (hq : q.Admissible) (a p₂ r beta : ℝ) :
    |errorUAt q a p₂ r beta| ≤ q.lambda⁻¹ * (40 * q.lambda)⁻¹ := by
  have hlam : 0 < q.lambda := hq.1
  have hC : 0 ≤ q.lambda⁻¹ * (40 * q.lambda)⁻¹ := by positivity
  have hint : |torusIntegral (fun t : ℝ => mixedRawErrorIntegrand q a p₂ r t beta)| ≤
      q.lambda⁻¹ * (40 * q.lambda)⁻¹ :=
    abs_torusIntegral_le (fun t => mixedRawErrorIntegrand_abs_le hq a p₂ r t beta)
  have hsin : |Real.sin beta ^ 2| ≤ 1 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [Real.neg_one_le_sin beta, Real.sin_le_one beta]
  have : errorUAt q a p₂ r beta =
      Real.sin beta ^ 2 *
        torusIntegral (fun t : ℝ => mixedRawErrorIntegrand q a p₂ r t beta) := rfl
  rw [this, abs_mul]
  calc |Real.sin beta ^ 2| * |torusIntegral (fun t : ℝ =>
        mixedRawErrorIntegrand q a p₂ r t beta)|
      ≤ 1 * (q.lambda⁻¹ * (40 * q.lambda)⁻¹) :=
        mul_le_mul hsin hint (abs_nonneg _) zero_le_one
    _ = q.lambda⁻¹ * (40 * q.lambda)⁻¹ := one_mul _

theorem errorUAt_nonneg {q : Parameters} (hq : q.Admissible) (a p₂ r beta : ℝ) :
    0 ≤ errorUAt q a p₂ r beta := by
  have hlam : 0 < q.lambda := hq.1
  refine mul_nonneg (sq_nonneg _) (torusIntegral_nonneg' fun t => ?_)
  split_ifs with h
  · exact mul_nonneg (correctionV_nonneg hq a t beta) (inv_multiplier_nonneg hlam _)
  · exact le_rfl

theorem measurableSet_errorSupport₂ (q : Parameters) (a p₂ : ℝ) :
    MeasurableSet {w : (ℝ × ℝ) × ℝ |
      w.1.1 + w.2 - p₂ ∈ correctionInterval q a w.2 w.1.2} := by
  unfold correctionInterval Parameters.supportInterval Parameters.delta Parameters.r0
  simp only [Set.mem_ite_empty_right, Set.mem_Icc]
  measurability

theorem measurable_inv_multiplier_comp₂ {α : Type*} [MeasurableSpace α]
    (q : Parameters) {b g : α → ℝ} (hb : Measurable b) (hg : Measurable g) :
    Measurable fun x => (multiplier 40 q (mixedTotalFrequency (b x) (g x)))⁻¹ := by
  unfold multiplier theta mixedTotalFrequency dispersion
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  fun_prop

theorem measurable_errorUAt (q : Parameters) (a p₂ : ℝ) :
    Measurable fun z : ℝ × ℝ => errorUAt q a p₂ z.1 z.2 := by
  have hinner : Measurable fun w : (ℝ × ℝ) × ℝ =>
      (if w.1.1 + w.2 - p₂ ∈ correctionInterval q a w.2 w.1.2 then
        correctionV 40 q a w.2 w.1.2 *
          (multiplier 40 q (mixedTotalFrequency w.1.2 (w.1.1 + w.2 - p₂)))⁻¹
      else 0) := by
    refine Measurable.ite (measurableSet_errorSupport₂ q a p₂) ?_ measurable_const
    refine Measurable.mul ?_ ?_
    · exact (correctionV_measurable 40 q a).comp
        (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
    · exact measurable_inv_multiplier_comp₂ q
        (measurable_snd.comp measurable_fst)
        (((measurable_fst.comp measurable_fst).add measurable_snd).sub_const p₂)
  have hI := torusIntegral_measurable_prod
    (f := fun (z : ℝ × ℝ) (t : ℝ) =>
      if z.1 + t - p₂ ∈ correctionInterval q a t z.2 then
        correctionV 40 q a t z.2 *
          (multiplier 40 q (mixedTotalFrequency z.2 (z.1 + t - p₂)))⁻¹
      else 0) hinner
  have : (fun z : ℝ × ℝ => errorUAt q a p₂ z.1 z.2) =
      fun z : ℝ × ℝ => Real.sin z.2 ^ 2 * torusIntegral (fun t : ℝ =>
        if z.1 + t - p₂ ∈ correctionInterval q a t z.2 then
          correctionV 40 q a t z.2 *
            (multiplier 40 q (mixedTotalFrequency z.2 (z.1 + t - p₂)))⁻¹
        else 0) := rfl
  rw [this]
  exact ((Real.measurable_sin.comp measurable_snd).pow_const 2).mul hI

theorem mixedHMinusWeight_nonneg {q : Parameters} (hq : q.Admissible) (r beta : ℝ) :
    0 ≤ mixedHMinusWeight q r beta := by
  rw [mixedHMinusWeight]
  have := mixed_denominator_pos hq.1 r beta
  positivity

theorem mixedHMinusWeight_le_inv {q : Parameters} (hq : q.Admissible) (r beta : ℝ) :
    mixedHMinusWeight q r beta ≤ q.lambda⁻¹ := by
  rw [mixedHMinusWeight]
  refine inv_anti₀ hq.1 ?_
  linarith [dispersion_nonneg r, dispersion_nonneg beta]

theorem mixedHMinusWeight_mul_correctionB {q : Parameters} (hq : q.Admissible)
    (r beta : ℝ) : mixedHMinusWeight q r beta * correctionB q r beta = 1 := by
  rw [mixedHMinusWeight, correctionB]
  exact inv_mul_cancel₀ (ne_of_gt (mixed_denominator_pos hq.1 r beta))

theorem correctionB_le_five {q : Parameters} (hq : q.Admissible) (r beta : ℝ) :
    correctionB q r beta ≤ 5 := by
  rw [correctionB]
  linarith [dispersion_le_two r, dispersion_le_two beta, hq.2.1]

/-! ### The mixed raw residual energy -/

/-- The squared `H⁻¹` norm of the mixed residual `w - D̃₂*k̃`. -/
def mixedRawResidualHMinusSq (q : Parameters) (a p₂ : ℝ) : ℝ :=
  torusIntegral fun beta => torusIntegral fun r =>
    mixedHMinusWeight q r beta * ‖mixedRawResidual q a p₂ r beta‖ ^ 2

/-- The desired term `B|v|²` of `(reduce)`, in the `(β,r)` order. -/
def mixedBEnergyIntegrand (q : Parameters) (a : ℝ) (beta r : ℝ) : ℝ :=
  correctionB q r beta * correctionV 40 q a r beta ^ 2

/-- The error term of `(reduce)`, in the `(β,r)` order. -/
def mixedErrorEnergyIntegrand (q : Parameters) (a p₂ : ℝ) (beta r : ℝ) : ℝ :=
  mixedHMinusWeight q r beta * errorUAt q a p₂ r beta ^ 2

theorem measurable_swapProd : Measurable (fun z : ℝ × ℝ => (z.2, z.1)) :=
  measurable_snd.prodMk measurable_fst

theorem measurable_errorUAt_swap (q : Parameters) (a p₂ : ℝ) :
    Measurable fun z : ℝ × ℝ => errorUAt q a p₂ z.2 z.1 := by
  have h := (measurable_errorUAt q a p₂).comp measurable_swapProd
  exact h

theorem measurable_correctionV_swap (q : Parameters) (a : ℝ) :
    Measurable fun z : ℝ × ℝ => correctionV 40 q a z.2 z.1 := by
  have h := (correctionV_measurable 40 q a).comp measurable_swapProd
  exact h

theorem measurable_mixedBEnergyIntegrand (q : Parameters) (a : ℝ) :
    Measurable fun z : ℝ × ℝ => mixedBEnergyIntegrand q a z.1 z.2 := by
  have hB : Measurable fun z : ℝ × ℝ => correctionB q z.2 z.1 := by
    unfold correctionB dispersion; fun_prop
  have hV : Measurable fun z : ℝ × ℝ => correctionV 40 q a z.2 z.1 :=
    measurable_correctionV_swap q a
  exact hB.mul (hV.pow_const 2)

theorem mixedBEnergyIntegrand_nonneg {q : Parameters} (hq : q.Admissible)
    (a beta r : ℝ) : 0 ≤ mixedBEnergyIntegrand q a beta r :=
  mul_nonneg (mixed_denominator_pos hq.1 r beta).le (sq_nonneg _)

theorem mixedBEnergyIntegrand_abs_le {q : Parameters} (hq : q.Admissible)
    (a beta r : ℝ) :
    |mixedBEnergyIntegrand q a beta r| ≤ 5 * (q.lambda⁻¹ * q.lambda⁻¹) := by
  have hlam : 0 < q.lambda := hq.1
  have hv0 := correctionV_nonneg hq a r beta
  have hv := correctionV_le_inv hq a r beta
  rw [abs_of_nonneg (mixedBEnergyIntegrand_nonneg hq a beta r), mixedBEnergyIntegrand]
  have hsq : correctionV 40 q a r beta ^ 2 ≤ q.lambda⁻¹ * q.lambda⁻¹ := by nlinarith
  exact mul_le_mul (correctionB_le_five hq r beta) hsq (sq_nonneg _) (by norm_num)

theorem measurable_mixedErrorEnergyIntegrand (q : Parameters) (a p₂ : ℝ) :
    Measurable fun z : ℝ × ℝ => mixedErrorEnergyIntegrand q a p₂ z.1 z.2 := by
  have hW : Measurable fun z : ℝ × ℝ => mixedHMinusWeight q z.2 z.1 := by
    unfold mixedHMinusWeight dispersion; fun_prop
  have hU : Measurable fun z : ℝ × ℝ => errorUAt q a p₂ z.2 z.1 :=
    measurable_errorUAt_swap q a p₂
  exact hW.mul (hU.pow_const 2)

theorem mixedErrorEnergyIntegrand_nonneg {q : Parameters} (hq : q.Admissible)
    (a p₂ beta r : ℝ) : 0 ≤ mixedErrorEnergyIntegrand q a p₂ beta r :=
  mul_nonneg (mixedHMinusWeight_nonneg hq r beta) (sq_nonneg _)

theorem mixedErrorEnergyIntegrand_abs_le {q : Parameters} (hq : q.Admissible)
    (a p₂ beta r : ℝ) :
    |mixedErrorEnergyIntegrand q a p₂ beta r| ≤
      q.lambda⁻¹ * ((q.lambda⁻¹ * (40 * q.lambda)⁻¹) * (q.lambda⁻¹ * (40 * q.lambda)⁻¹)) := by
  have hlam : 0 < q.lambda := hq.1
  have hU0 := errorUAt_nonneg hq a p₂ r beta
  have hU := errorUAt_abs_le hq a p₂ r beta
  rw [abs_of_nonneg hU0] at hU
  rw [abs_of_nonneg (mixedErrorEnergyIntegrand_nonneg hq a p₂ beta r),
    mixedErrorEnergyIntegrand]
  have hsq : errorUAt q a p₂ r beta ^ 2 ≤
      (q.lambda⁻¹ * (40 * q.lambda)⁻¹) * (q.lambda⁻¹ * (40 * q.lambda)⁻¹) := by
    nlinarith
  exact mul_le_mul (mixedHMinusWeight_le_inv hq r beta) hsq (sq_nonneg _)
    (by positivity)

/-! ### Step 4: the reduction (reduce) for the raw mixed residual -/

theorem mixedRawResidual_integrand_le {q : Parameters} (hq : q.Admissible)
    {a p₂ : ℝ} (ha : 0 ≤ a) (hp₂ : |p₂| ≤ a) (beta r : ℝ) :
    mixedHMinusWeight q r beta * ‖mixedRawResidual q a p₂ r beta‖ ^ 2 ≤
      2 * mixedBEnergyIntegrand q a beta r +
        2 * mixedErrorEnergyIntegrand q a p₂ beta r := by
  rw [mixedRawResidual_eq hq ha hp₂, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    mixedBEnergyIntegrand, mixedErrorEnergyIntegrand]
  have hWB : mixedHMinusWeight q r beta * correctionB q r beta = 1 :=
    mixedHMinusWeight_mul_correctionB hq r beta
  have hW0 : 0 ≤ mixedHMinusWeight q r beta := mixedHMinusWeight_nonneg hq r beta
  set W := mixedHMinusWeight q r beta
  set B := correctionB q r beta
  set v := correctionV 40 q a r beta
  set U := errorUAt q a p₂ r beta
  have key : 0 ≤ W * (B * v + U) ^ 2 := mul_nonneg hW0 (sq_nonneg _)
  have hzero : 2 * B * v ^ 2 * (1 - W * B) = 0 := by rw [hWB]; ring
  nlinarith [key, hzero]

theorem torusIntegral₂_mixedBEnergyIntegrand {q : Parameters} (hq : q.Admissible)
    (a : ℝ) :
    (torusIntegral fun beta => torusIntegral fun r =>
        mixedBEnergyIntegrand q a beta r) = correctionBEnergy q a := by
  rw [torusIntegral₂_swap (measurable_mixedBEnergyIntegrand q a)
    (fun x y => mixedBEnergyIntegrand_abs_le hq a x y)]
  rfl

theorem mixedErrorEnergy_inner_eq {q : Parameters} (hq : q.Admissible)
    {a p₂ : ℝ} (ha : 0 ≤ a) (hp₂ : |p₂| ≤ a) (beta : ℝ) :
    (torusIntegral fun r => mixedErrorEnergyIntegrand q a p₂ beta r) =
      torusIntegral (fun s => if 0 < s then
        mixedHMinusWeight q (-s) beta * errorU q a p₂ s beta ^ 2 else 0) := by
  have hfun : (fun s : ℝ => mixedErrorEnergyIntegrand q a p₂ beta (-s)) =
      (fun s : ℝ => if 0 < s then
        mixedHMinusWeight q (-s) beta * errorU q a p₂ s beta ^ 2 else 0) := by
    funext s
    by_cases hs : 0 < s
    · rw [if_pos hs]
      rfl
    · rw [if_neg hs, mixedErrorEnergyIntegrand,
        errorUAt_eq_zero_of_nonneg hq ha hp₂ (by linarith [not_lt.mp hs]) beta]
      ring
  calc (torusIntegral fun r => mixedErrorEnergyIntegrand q a p₂ beta r)
      = torusIntegral (fun s => mixedErrorEnergyIntegrand q a p₂ beta (-s)) :=
        (torusIntegral_neg _).symm
    _ = _ := by rw [hfun]

theorem torusIntegral₂_mixedErrorEnergyIntegrand {q : Parameters}
    (hq : q.Admissible) {a p₂ : ℝ} (ha : 0 ≤ a) (hp₂ : |p₂| ≤ a) :
    (torusIntegral fun beta => torusIntegral fun r =>
        mixedErrorEnergyIntegrand q a p₂ beta r) = errorHMinusSq q a p₂ := by
  unfold errorHMinusSq
  simp only [mixedErrorEnergy_inner_eq hq ha hp₂]

/-- **Steps 2--4 of Lemma 5.4, scalar form.**  The squared `H⁻¹` norm of the
mixed residual `w - D̃₂*k̃` is at most twice the on-support term `∫∫B|v|²` plus
twice the error term `‖U‖²_{-1}`. -/
theorem mixedRawResidualHMinusSq_le_energies {q : Parameters} (hq : q.Admissible)
    {a p₂ : ℝ} (ha : 0 ≤ a) (hp₂ : |p₂| ≤ a) :
    mixedRawResidualHMinusSq q a p₂ ≤
      2 * correctionBEnergy q a + 2 * errorHMinusSq q a p₂ := by
  have hlam : 0 < q.lambda := hq.1
  set C1 : ℝ := 5 * (q.lambda⁻¹ * q.lambda⁻¹) with hC1
  set C2 : ℝ := q.lambda⁻¹ *
    ((q.lambda⁻¹ * (40 * q.lambda)⁻¹) * (q.lambda⁻¹ * (40 * q.lambda)⁻¹)) with hC2
  have hmB : Measurable fun z : ℝ × ℝ => 2 * mixedBEnergyIntegrand q a z.1 z.2 :=
    measurable_const.mul (measurable_mixedBEnergyIntegrand q a)
  have hmE : Measurable fun z : ℝ × ℝ =>
      2 * mixedErrorEnergyIntegrand q a p₂ z.1 z.2 :=
    measurable_const.mul (measurable_mixedErrorEnergyIntegrand q a p₂)
  have hbB : ∀ x y, |2 * mixedBEnergyIntegrand q a x y| ≤ 2 * C1 := by
    intro x y
    rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    exact mul_le_mul_of_nonneg_left (mixedBEnergyIntegrand_abs_le hq a x y)
      (by norm_num)
  have hbE : ∀ x y, |2 * mixedErrorEnergyIntegrand q a p₂ x y| ≤ 2 * C2 := by
    intro x y
    rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    exact mul_le_mul_of_nonneg_left (mixedErrorEnergyIntegrand_abs_le hq a p₂ x y)
      (by norm_num)
  have hsum : (torusIntegral fun beta => torusIntegral fun r =>
        (2 * mixedBEnergyIntegrand q a beta r +
          2 * mixedErrorEnergyIntegrand q a p₂ beta r)) =
      (torusIntegral fun beta => torusIntegral fun r =>
          2 * mixedBEnergyIntegrand q a beta r) +
        torusIntegral fun beta => torusIntegral fun r =>
          2 * mixedErrorEnergyIntegrand q a p₂ beta r :=
    torusIntegral₂_add hmB hbB hmE hbE
  have hmono : mixedRawResidualHMinusSq q a p₂ ≤
      torusIntegral fun beta => torusIntegral fun r =>
        (2 * mixedBEnergyIntegrand q a beta r +
          2 * mixedErrorEnergyIntegrand q a p₂ beta r) := by
    refine torusIntegral₂_mono (C := 2 * C1 + 2 * C2) ?_ ?_ ?_ ?_
    · exact hmB.add hmE
    · intro x y
      exact le_trans (abs_add_le _ _) (add_le_add (hbB x y) (hbE x y))
    · intro x y
      exact mul_nonneg (mixedHMinusWeight_nonneg hq y x) (sq_nonneg _)
    · intro x y
      exact mixedRawResidual_integrand_le hq ha hp₂ x y
  rw [hsum] at hmono
  simp only [torusIntegral_smul_left] at hmono
  rw [torusIntegral₂_mixedBEnergyIntegrand hq a,
    torusIntegral₂_mixedErrorEnergyIntegrand hq ha hp₂] at hmono
  exact hmono

/-- **Equation (reduce)** for the mixed residual: both scalar energies are at
most the single reduced integral `∫_I∫ dm/(B+σ)` of `manuscript.tex:1409-1418`.
-/
theorem mixedRawResidualHMinusSq_le_reducedIntegral {q : Parameters}
    (hq : q.Admissible) {a p₂ : ℝ} (ha : 0 ≤ a) (hp₂ : |p₂| ≤ a) :
    mixedRawResidualHMinusSq q a p₂ ≤
      (2 + 2 * errorKernelConstant q) * correctionReducedIntegral q a := by
  have h1 := mixedRawResidualHMinusSq_le_energies hq ha hp₂
  have h2 := correctionBEnergy_le_reducedIntegral hq.1 (a := a)
  have h3 : errorHMinusSq q a p₂ ≤
      errorKernelConstant q * correctionSigmaEnergy q a :=
    errorHMinusSq_le_rowOrder hq ha hp₂
  have h4 := correctionSigmaEnergy_le_reducedIntegral hq.1 (a := a)
  have hk : 0 ≤ errorKernelConstant q := (errorKernelConstant_pos hq).le
  nlinarith [h1, h2, h3, h4, hk]

/-- **Lemma 5.4 for the raw mixed residual.**  Proposition 4.2 turns the two
scalar energies into `C √L`. -/
theorem mixedRawResidualHMinusSq_le_sqrtScale {q : Parameters} (hq : q.Admissible)
    {C a p₂ : ℝ} (ha : 0 ≤ a) (hp₂ : |p₂| ≤ a)
    (hfive : PropositionFiveTwoIntegralBound 40 C q a) :
    mixedRawResidualHMinusSq q a p₂ ≤
      (2 + 2 * errorKernelConstant q) * C * Real.sqrt (q.scaleLog a) := by
  have h1 := mixedRawResidualHMinusSq_le_energies hq ha hp₂
  have h2 : correctionBEnergy q a ≤ C * Real.sqrt (q.scaleLog a) :=
    correctionBEnergy_le_sqrtScale hq.1 hfive
  have h3 : errorHMinusSq q a p₂ ≤
      errorKernelConstant q * correctionSigmaEnergy q a :=
    errorHMinusSq_le_rowOrder hq ha hp₂
  have h4 : correctionSigmaEnergy q a ≤ C * Real.sqrt (q.scaleLog a) :=
    correctionSigmaEnergy_le_sqrtScale hq.1 hfive
  have hk : 0 ≤ errorKernelConstant q := (errorKernelConstant_pos hq).le
  nlinarith [h1, h2, h3, h4, hk]

/-! ### The two-row component of `D̃₂*k̃` vanishes -/

theorem torusIntegral_of_odd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {g : ℝ → E} (hg : ∀ s, g (-s) = -g s) :
    torusIntegral g = 0 := by
  have h1 : (torusIntegral fun s => g (-s)) = torusIntegral g := torusIntegral_neg g
  have h2 : (torusIntegral fun s => g (-s)) = -torusIntegral g := by
    simp only [hg]
    rw [torusIntegral, torusIntegral, integral_neg, smul_neg]
  rw [h1] at h2
  have : (2 : ℝ) • torusIntegral g = 0 := by
    rw [two_smul]
    nth_rewrite 2 [h2]
    simp
  simpa using this

theorem dispersion_neg (s : ℝ) : dispersion (-s) = dispersion s := by
  rw [dispersion, dispersion, Real.cos_neg]

theorem multiplier_mixed_neg (q : Parameters) (beta alpha : ℝ) :
    multiplier 40 q (mixedTotalFrequency (-beta) alpha) =
      multiplier 40 q (mixedTotalFrequency beta alpha) := by
  unfold multiplier theta mixedTotalFrequency
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [dispersion_neg, show -beta / 2 = -(beta / 2) by ring, Real.sin_neg, abs_neg]

theorem correctionInterval_neg (q : Parameters) (a r beta : ℝ) :
    correctionInterval q a r (-beta) = correctionInterval q a r beta := by
  unfold correctionInterval
  rw [abs_neg]

theorem correctionSigma_neg (q : Parameters) (a r beta : ℝ) :
    correctionSigma 40 q a r (-beta) = correctionSigma 40 q a r beta := by
  unfold correctionSigma
  rw [Real.sin_neg, neg_pow, correctionInterval_neg]
  simp only [multiplier_mixed_neg]
  norm_num

theorem correctionB_neg (q : Parameters) (r beta : ℝ) :
    correctionB q r (-beta) = correctionB q r beta := by
  rw [correctionB, correctionB, dispersion_neg]

theorem correctionV_neg (q : Parameters) (a r beta : ℝ) :
    correctionV 40 q a r (-beta) = correctionV 40 q a r beta := by
  unfold correctionV
  rw [correctionB_neg, correctionSigma_neg]

/-- Every factor of the explicit correction except `sin β` is even in `β`. -/
theorem correctionCoefficient_neg_beta (q : Parameters) (a p₂ r r' beta : ℝ) :
    correctionCoefficient 40 q a p₂ r r' (-beta) =
      -correctionCoefficient 40 q a p₂ r r' beta := by
  simp only [correctionCoefficient]
  rw [Real.sin_neg, multiplier_mixed_neg, correctionV_neg, correctionV_neg,
    correctionInterval_neg, correctionInterval_neg]
  push_cast
  ring

/-- **Step 2 of Lemma 5.4, first clause.**  `D̃₂*k̃` has no two-row
component.
-/
theorem rawD2StarTwoRow_correctionCoefficient (q : Parameters) (a p₂ r r' : ℝ) :
    rawD2StarTwoRow p₂ (correctionCoefficient 40 q a p₂) r r' = 0 := by
  rw [rawD2StarTwoRow,
    torusIntegral_of_odd (fun beta => correctionCoefficient_neg_beta q a p₂ r r' beta)]
  ring

end ScalarStepTwo

/-! ## The two-row Walsh component of `D₂*k_p`

The frequency-side statement `rawD2StarTwoRow_correctionCoefficient` above is
Step 2's first clause for the *scalar* kernel.  This section carries it to the
actual competitor: the Walsh vector `k_p` of `Glue/Correction.lean` is the
type-`112` synthesis of `Manhattan.correctionType112Coefficients`, an `ℓ²`
element obtained as `Π₃` of the three-dimensional Fourier coefficients of
`Manhattan.rawCorrectionFunction`, so the finitely supported statements of
`Manhattan/Glue/ConcreteLoweringFourier.lean` do not apply to it.  What does
apply is the `L²` lowering formula (D2a),
`Manhattan.Glue.type112DStarTwoRow_eq`, which expresses the two-row
coefficient of `D₂*` through two Walsh coefficients of the input whose
*column* index is zero.  Since `k̃` is odd in the column frequency `β`
(`correctionCoefficient_neg_beta`), every Fourier coefficient of the raw
correction at column index zero vanishes, and with it the whole two-row
component of `D₂*k_p`.

Paper: `manuscript.tex:1332-1346`.
-/

section TwoRowWalsh

open Manhattan.Estimates

attribute [local instance] cubicUnitAddCircleMeasureSpace

/-- `mFourier` written in the angle coordinates of the paper's torus. -/
theorem mFourier_eq_exp_angle {n : ℕ} (m : Fin n → ℤ) (t : UnitAddTorus (Fin n)) :
    UnitAddTorus.mFourier m t =
      Complex.exp (Complex.I *
        ((∑ a : Fin n, (m a : ℝ) * Manhattan.unitTorusAngle (t a) : ℝ) : ℂ)) := by
  classical
  choose k hk using fun a : Fin n => two_pi_torusLift (t a)
  rw [mFourier_eq_exp]
  have hsum : (2 * Real.pi * ∑ a : Fin n, (m a : ℝ) * torusLift (t a) : ℝ)
      = (∑ a : Fin n, (m a : ℝ) * Manhattan.unitTorusAngle (t a))
        + ((∑ a : Fin n, m a * k a : ℤ) : ℝ) * (2 * Real.pi) := by
    have hterm : ∀ a : Fin n, (m a : ℝ) * (2 * Real.pi * torusLift (t a))
        = (m a : ℝ) * Manhattan.unitTorusAngle (t a)
          + ((m a : ℝ) * (k a : ℝ)) * (2 * Real.pi) := by
      intro a
      rw [hk a]
      ring
    calc (2 * Real.pi * ∑ a : Fin n, (m a : ℝ) * torusLift (t a) : ℝ)
        = ∑ a : Fin n, (m a : ℝ) * (2 * Real.pi * torusLift (t a)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun a _ => by ring
      _ = ∑ a : Fin n, ((m a : ℝ) * Manhattan.unitTorusAngle (t a)
            + ((m a : ℝ) * (k a : ℝ)) * (2 * Real.pi)) :=
          Finset.sum_congr rfl fun a _ => hterm a
      _ = _ := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul]
          push_cast
          ring
  rw [hsum]
  have hsplit : Complex.I *
        (((∑ a : Fin n, (m a : ℝ) * Manhattan.unitTorusAngle (t a))
          + ((∑ a : Fin n, m a * k a : ℤ) : ℝ) * (2 * Real.pi) : ℝ) : ℂ)
      = Complex.I *
          ((∑ a : Fin n, (m a : ℝ) * Manhattan.unitTorusAngle (t a) : ℝ) : ℂ)
        + ((∑ a : Fin n, m a * k a : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [hsplit, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- A continuous real-linear functional commutes with the normalized torus
integral. -/
theorem map_torusIntegral (L : ℂ →L[ℝ] ℝ) {g : ℝ → ℂ}
    (hg : IntegrableOn g Estimates.torus) :
    Estimates.torusIntegral (fun x => L (g x)) = L (Estimates.torusIntegral g) := by
  rw [Estimates.torusIntegral, Estimates.torusIntegral, map_smul,
    ← L.integral_comp_comm hg]

attribute [local instance] Real.fact_zero_lt_one

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- A bounded measurable function of the three angle coordinates whose
innermost normalized torus integral vanishes integrates to zero on the
three-dimensional Fourier torus. -/
theorem integral_unitTorus_three_eq_zero {F : ℝ → ℝ → ℝ → ℂ}
    (hF : Measurable fun z : ℝ × ℝ × ℝ => F z.1 z.2.1 z.2.2)
    {C : ℝ} (hb : ∀ r r' b, ‖F r r' b‖ ≤ C)
    (hzero : ∀ r r' : ℝ, Estimates.torusIntegral (fun b => F r r' b) = 0) :
    (∫ x : UnitAddTorus (Fin 3),
        F (Manhattan.unitTorusAngle (x 0)) (Manhattan.unitTorusAngle (x 1))
          (Manhattan.unitTorusAngle (x 2))) = 0 := by
  have h0 : Measurable fun x : UnitAddTorus (Fin 3) =>
      Manhattan.unitTorusAngle (x 0) :=
    Manhattan.unitTorusAngle_measurable.comp (measurable_pi_apply 0)
  have h1 : Measurable fun x : UnitAddTorus (Fin 3) =>
      Manhattan.unitTorusAngle (x 1) :=
    Manhattan.unitTorusAngle_measurable.comp (measurable_pi_apply 1)
  have h2 : Measurable fun x : UnitAddTorus (Fin 3) =>
      Manhattan.unitTorusAngle (x 2) :=
    Manhattan.unitTorusAngle_measurable.comp (measurable_pi_apply 2)
  have hcoord : Measurable fun x : UnitAddTorus (Fin 3) =>
      ((Manhattan.unitTorusAngle (x 0), Manhattan.unitTorusAngle (x 1),
        Manhattan.unitTorusAngle (x 2)) : ℝ × ℝ × ℝ) := h0.prodMk (h1.prodMk h2)
  have hmeasT : Measurable fun x : UnitAddTorus (Fin 3) =>
      F (Manhattan.unitTorusAngle (x 0)) (Manhattan.unitTorusAngle (x 1))
        (Manhattan.unitTorusAngle (x 2)) := hF.comp hcoord
  have hint : Integrable (fun x : UnitAddTorus (Fin 3) =>
      F (Manhattan.unitTorusAngle (x 0)) (Manhattan.unitTorusAngle (x 1))
        (Manhattan.unitTorusAngle (x 2))) :=
    Integrable.mono' (integrable_const C) hmeasT.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => hb _ _ _)
  have key : ∀ L : ℂ →L[ℝ] ℝ,
      (∫ x : UnitAddTorus (Fin 3),
        L (F (Manhattan.unitTorusAngle (x 0)) (Manhattan.unitTorusAngle (x 1))
          (Manhattan.unitTorusAngle (x 2)))) = 0 := by
    intro L
    have hmeasL : Measurable fun z : ℝ × ℝ × ℝ => L (F z.1 z.2.1 z.2.2) :=
      L.continuous.measurable.comp hF
    have hbL : ∀ r r' b : ℝ, |L (F r r' b)| ≤ ‖L‖ * C := by
      intro r r' b
      have h1 : ‖L (F r r' b)‖ ≤ ‖L‖ * ‖F r r' b‖ := L.le_opNorm _
      have h2 : ‖L‖ * ‖F r r' b‖ ≤ ‖L‖ * C :=
        mul_le_mul_of_nonneg_left (hb r r' b) (norm_nonneg L)
      simpa [Real.norm_eq_abs] using h1.trans h2
    have hinner : ∀ r r' : ℝ,
        Estimates.torusIntegral (fun b => L (F r r' b)) = 0 := by
      intro r r'
      have hmeasb : Measurable fun b : ℝ => F r r' b :=
        hF.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
      have hgint : IntegrableOn (fun b => F r r' b) Estimates.torus :=
        Integrable.mono' (integrable_const C) hmeasb.aestronglyMeasurable
          (Filter.Eventually.of_forall fun b => hb _ _ _)
      rw [map_torusIntegral L hgint, hzero r r', map_zero]
    rw [integral_unitTorus_three (fun r r' b => L (F r r' b)) hmeasL hbL]
    simp only [hinner]
    simp [Estimates.torusIntegral]
  have hre := key Complex.reCLM
  have him := key Complex.imCLM
  apply Complex.ext
  · rw [Complex.zero_re, ← hre]
    exact (Complex.reCLM.integral_comp_comm hint).symm
  · rw [Complex.zero_im, ← him]
    exact (Complex.imCLM.integral_comp_comm hint).symm

/-! ### The Fourier coefficients of the correction at column index zero -/

/-- Every factor of the explicit correction except `sin β` is even in `β`, so
its normalized `β`-integral vanishes. -/
theorem torusIntegral_correctionCoefficient_beta (q : Parameters) (a p₂ r r' : ℝ) :
    Estimates.torusIntegral
        (fun beta => correctionCoefficient 40 q a p₂ r r' beta) = 0 :=
  torusIntegral_of_odd fun beta => correctionCoefficient_neg_beta q a p₂ r r' beta

/-- **The column-zero Fourier coefficients of the raw correction vanish.**
The manuscript's `k̃` is odd in the column frequency `β`, so every
three-dimensional Fourier coefficient whose column index is zero is zero.
This is the coefficient form of `rawD2StarTwoRow_correctionCoefficient`. -/
theorem mFourierCoeff_rawCorrection_eq_zero {q : Parameters}
    (hlambda : 0 < q.lambda) (a p₂ : ℝ) {n : Manhattan.RawType112Index}
    (hn : n 2 = 0) :
    UnitAddTorus.mFourierCoeff
        ((Manhattan.rawCorrectionL2 (kappa := 40) (by norm_num) hlambda a p₂ :
          UnitAddTorus (Fin 3) → ℂ)) n = 0 := by
  classical
  set F : ℝ → ℝ → ℝ → ℂ := fun s s' u =>
    Complex.exp (Complex.I * ((-(n 0 : ℝ) * s + -(n 1 : ℝ) * s' : ℝ) : ℂ)) *
      correctionCoefficient 40 q a p₂ s s' u with hFdef
  have hexpnorm : ∀ x : ℝ, ‖Complex.exp (Complex.I * ((x : ℝ) : ℂ))‖ = 1 := by
    intro x
    rw [Complex.norm_exp]
    simp
  have hcoeff : UnitAddTorus.mFourierCoeff
      ((Manhattan.rawCorrectionL2 (kappa := 40) (by norm_num) hlambda a p₂ :
        UnitAddTorus (Fin 3) → ℂ)) n
      = ∫ x : UnitAddTorus (Fin 3),
          F (Manhattan.unitTorusAngle (x 0)) (Manhattan.unitTorusAngle (x 1))
            (Manhattan.unitTorusAngle (x 2)) := by
    rw [UnitAddTorus.mFourierCoeff]
    refine integral_congr_ae ?_
    filter_upwards [(Manhattan.rawCorrectionFunction_memLp (kappa := 40)
      (by norm_num) hlambda a p₂).coeFn_toLp] with x hx
    have hx' : (Manhattan.rawCorrectionL2 (kappa := 40) (by norm_num)
        hlambda a p₂ : UnitAddTorus (Fin 3) → ℂ) x =
        Manhattan.rawCorrectionFunction 40 q a p₂ x := hx
    rw [hx', smul_eq_mul, mFourier_eq_exp_angle, hFdef]
    congr 2
    rw [Fin.sum_univ_three]
    simp only [Pi.neg_apply, hn]
    push_cast
    ring
  rw [hcoeff]
  have hmeas : Measurable fun z : ℝ × ℝ × ℝ => F z.1 z.2.1 z.2.2 := by
    have h1 : Measurable fun z : ℝ × ℝ × ℝ =>
        Complex.exp (Complex.I * ((-(n 0 : ℝ) * z.1 + -(n 1 : ℝ) * z.2.1 : ℝ) : ℂ)) := by
      fun_prop
    exact h1.mul (Manhattan.correctionCoefficient_measurable 40 q a p₂)
  have hbound : ∀ r r' b : ℝ,
      ‖F r r' b‖ ≤ ((40 : ℝ) * q.lambda)⁻¹ * (2 * q.lambda⁻¹) := by
    intro r r' b
    rw [hFdef]
    simp only [norm_mul, hexpnorm, one_mul]
    exact Manhattan.correctionCoefficient_norm_bound (by norm_num) hlambda a p₂ r r' b
  have hzero : ∀ r r' : ℝ, Estimates.torusIntegral (fun b => F r r' b) = 0 := by
    intro r r'
    rw [hFdef]
    simp only
    rw [torusIntegral_const_mul, torusIntegral_correctionCoefficient_beta, mul_zero]
  exact integral_unitTorus_three_eq_zero hmeas hbound hzero

/-! ### The two-row Walsh component of `D₂*k_p` -/

/-- The vertical line of a type-`(1,1,2)` Finset index is the one carried by
its ordered column coordinate. -/
theorem mem_vertical_type112RawIndex (S : Manhattan.Type112Index) :
    ((Axis.vertical, Manhattan.type112RawIndex S 2) : LineIndex) ∈ S.1 := by
  rw [← type112Lines_eq S]
  simp

/-- Reading the ordered column coordinate off an explicit triple. -/
theorem type112RawIndex_two_tripleToFinset {m m' c : ℤ}
    (h : IsType112Index (tripleToFinset (m, m', c))) :
    Manhattan.type112RawIndex ⟨tripleToFinset (m, m', c), h⟩ 2 = c := by
  have hmem := mem_vertical_type112RawIndex ⟨tripleToFinset (m, m', c), h⟩
  simp only [tripleToFinset, Finset.mem_insert, Finset.mem_singleton,
    Prod.mk.injEq] at hmem
  rcases hmem with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨_, h2⟩
  · exact absurd h1 (by simp)
  · exact absurd h1 (by simp)
  · exact h2

theorem correctionType112Coefficients_eq_zero_of_col {q : Parameters}
    (hlambda : 0 < q.lambda) (a p₂ : ℝ) {S : Manhattan.Type112Index}
    (hS : Manhattan.type112RawIndex S 2 = 0) :
    Manhattan.correctionType112Coefficients (kappa := 40) (by norm_num)
      hlambda a p₂ S = 0 := by
  rw [Manhattan.correctionType112Coefficients_apply]
  exact mFourierCoeff_rawCorrection_eq_zero hlambda a p₂ hS

/-- The projected correction has no Walsh coefficient at column index zero. -/
theorem type112CoefficientAt_correction_col_zero {q : Parameters}
    (hlambda : 0 < q.lambda) (a p₂ : ℝ) (m m' : ℤ) :
    type112CoefficientAt
        (Manhattan.correctionType112Coefficients (kappa := 40) (by norm_num)
          hlambda a p₂) (tripleToFinset (m, m', 0)) = 0 := by
  rw [type112CoefficientAt]
  by_cases h : IsType112Index (tripleToFinset (m, m', 0))
  · rw [dif_pos h]
    exact correctionType112Coefficients_eq_zero_of_col hlambda a p₂
      (type112RawIndex_two_tripleToFinset h)
  · rw [dif_neg h]

/-- **Step 2 of Lemma 5.4, first clause, at the Walsh level.**  The concrete
degree-two two-row component of `D₂*k_p` vanishes identically, for the
competitor's `ℓ²` coefficient `Π₃k̃` and at every frozen momentum.  The
frequency-side statement is `rawD2StarTwoRow_correctionCoefficient`; this is
its counterpart for the actual Walsh vector, obtained from the `L²` lowering
formula (D2a) of `Manhattan.Glue.type112DStarTwoRow_eq`. -/
theorem type112DStarTwoRow_correction_apply {q : Parameters}
    (hlambda : 0 < q.lambda) (a p₂ : ℝ) (p : Fin 2 → ℝ) (T : Type11Index) :
    Manhattan.type112DStarTwoRow p
      (Manhattan.correctionType112Coefficients (kappa := 40) (by norm_num)
        hlambda a p₂) T = 0 := by
  rw [type112DStarTwoRow_eq, type112CoefficientAt_correction_col_zero,
    type112CoefficientAt_correction_col_zero]
  ring

theorem type112DStarTwoRow_correction {q : Parameters}
    (hlambda : 0 < q.lambda) (a p₂ : ℝ) (p : Fin 2 → ℝ) :
    Manhattan.type112DStarTwoRow p
      (Manhattan.correctionType112Coefficients (kappa := 40) (by norm_num)
        hlambda a p₂) = 0 := by
  apply lp.ext
  funext T
  simpa using type112DStarTwoRow_correction_apply hlambda a p₂ p T

/-- The two-row Walsh coefficients of `A_p k_p` all vanish.
-/
theorem inner_type11_concreteFiberA_correctionWalsh {q : Parameters}
    (hlambda : 0 < q.lambda) (a p₂ : ℝ) (p : Fin 2 → ℝ) (T : Type11Index) :
    inner ℂ (Manhattan.walshL2 T.1)
      (Manhattan.concreteFiberA p
        (Manhattan.correctionWalsh (kappa := 40) (by norm_num)
          hlambda a p₂)) = 0 := by
  have h := type112DStarTwoRow_correction_apply hlambda a p₂ p T
  rw [Manhattan.type112DStarTwoRow, Manhattan.type11WalshAnalysis,
    Manhattan.walshSectorAnalysis_apply, inner_neg_right, neg_eq_zero] at h
  exact h

/-- `(D2a)` is linear in the type-`(1,1,2)` coefficient, so the manuscript's
`sgn(sin p₁)` multiplier passes through it. -/
theorem type112DStarTwoRow_smul (p : Fin 2 → ℝ) (z : ℂ)
    (c : ℓ²(Manhattan.Type112Index, ℂ)) :
    Manhattan.type112DStarTwoRow p (z • c) =
      z • Manhattan.type112DStarTwoRow p c := by
  have hL : ∀ T : Manhattan.Type11Index,
      Manhattan.type112DStarTwoRow p (z • c) T =
        z * Manhattan.type112DStarTwoRow p c T := by
    intro T
    rw [Manhattan.type112DStarTwoRow_apply, Manhattan.type112DStarTwoRow_apply,
      map_smul, inner_smul_right]
  apply lp.ext
  funext T
  simpa using hL T

/-- The (shift)-twisted projected correction has no two-row lowering
component. -/
theorem type112DStarTwoRow_shiftedCorrectionCoefficients {q : Parameters}
    (hkappa : (0 : ℝ) < 40) (hlambda : 0 < q.lambda) (a p₁ p₂ : ℝ)
    (p : Fin 2 → ℝ) :
    Manhattan.type112DStarTwoRow p
      (Manhattan.shiftedCorrectionType112Coefficients (kappa := 40) hkappa
        hlambda a p₁ p₂) = 0 := by
  have hcol : ∀ m m' : ℤ, type112CoefficientAt
      (Manhattan.shiftedCorrectionType112Coefficients (kappa := 40) hkappa
        hlambda a p₁ p₂) (tripleToFinset (m, m', 0)) = 0 := by
    intro m m'
    rw [type112CoefficientAt]
    by_cases h : IsType112Index (tripleToFinset (m, m', 0))
    · rw [dif_pos h]
      exact Manhattan.type112ShiftTwist_eq_zero
        (correctionType112Coefficients_eq_zero_of_col hlambda a p₂
          (type112RawIndex_two_tripleToFinset h))
    · rw [dif_neg h]
  apply lp.ext
  funext T
  have hT := type112DStarTwoRow_eq p
    (Manhattan.shiftedCorrectionType112Coefficients (kappa := 40) hkappa
      hlambda a p₁ p₂) T
  simp only [hcol] at hT
  simpa using hT

/-- The competitor's own degree-three coefficient has no two-row lowering
component. -/
theorem type112DStarTwoRow_correctedLowDegreeData {q : Parameters}
    (hlambda : 0 < q.lambda) (p : Fin 2 → ℝ)
    (hcert : Estimates.LemmaFourTwoIntegralCertificate q (p 0) (p 1))
    (hnormalization : Estimates.degreeOneNormalization q (p 0) ≠ 0) :
    Manhattan.type112DStarTwoRow p
      (correctedLowDegreeData hlambda p hcert hnormalization).mixedCoefficient = 0 := by
  rw [correctedLowDegreeData_mixedCoefficient_eq, type112DStarTwoRow_smul,
    type112DStarTwoRow_shiftedCorrectionCoefficients, smul_zero]

end TwoRowWalsh

/-! ## The degree-two sector of the concrete residual

Summand 3 is the dual energy of the degree-two Walsh sector of
`b_p·1-A_p(f_p+k_p)`, which by
`Manhattan.Glue.walshSectorComponent_two_unnormalizedResidual` is the
degree-two sector of `-A_p(f_p+k_p)`.  This section splits that sector into
the two axis patterns which actually occur.

A two-element Walsh index is two rows, one row and one column, or two
columns.  The last case never occurs here: raising a row-supported degree-one
vector always keeps the row it started from
(`inner_verticalPair_walshRaise_axisDegreeOne`), and lowering a type-`(1,1,2)`
vector always leaves at least one row
(`inner_verticalPair_concreteFiberA_type112`).  So the sector is the
orthogonal sum of a two-row and a mixed Walsh vector
(`walshSectorComponent_two_eq_type11_add_type12`), and the parallelogram
bound `Manhattan.Glue.hMinusEnergy_add_le` reduces summand 3 to one bound per
sector (`summandThreeBound_of_sector_bounds`).

Both sectors are computed here at the level of Walsh coefficients.  The
two-row coefficient is `i sin(p₁)` times a single degree-one coefficient
(`inner_rowPair_walshRaise_axisDegreeOne`): in the Finset convention of
the manuscript's symmetrization `f(r)+f(r')` in (D2a) is
replaced by the term whose omitted line is the origin row.  The mixed
coefficient is the Walsh form of the manuscript's `(onI)`
(`type12WalshAnalysis_sub_type112DStarMixed_apply`): the raising half lives
entirely at column index zero, which is the statement that `w(r,β)=i sin(r)f(r)`
does not depend on `β`, and the lowering half is (D2b) of
`Manhattan.Glue.type112DStarMixed_eq`.

Paper: `manuscript.tex:762-790` (the four-sector form (22)),
`manuscript.tex:793-822` ((D2a), (D2b)), `manuscript.tex:1332-1420`
(Lemma 5.4).
-/

section DegreeTwoSectorSplit

/-- A two-element Walsh index is either two rows, or mixed, or two columns. -/
theorem isType11_or_isType12_or_vertical {S : Finset LineIndex} (hS : S.card = 2) :
    IsType11Index S ∨ IsType12Index S ∨ ∀ l ∈ S, l.1 = Manhattan.Axis.vertical := by
  classical
  have hsub := Finset.card_filter_le S (fun l : LineIndex => l.1 = Manhattan.Axis.horizontal)
  rw [hS] at hsub
  by_cases h2 : (S.filter fun l : LineIndex => l.1 = Manhattan.Axis.horizontal).card = 2
  · refine Or.inl ⟨hS, ?_⟩
    have heq : S.filter (fun l : LineIndex => l.1 = Manhattan.Axis.horizontal) = S :=
      Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by rw [hS, h2])
    intro l hl
    rw [← heq] at hl
    exact (Finset.mem_filter.mp hl).2
  by_cases h1 : (S.filter fun l : LineIndex => l.1 = Manhattan.Axis.horizontal).card = 1
  · exact Or.inr (Or.inl ⟨hS, h1⟩)
  refine Or.inr (Or.inr ?_)
  have h0 : (S.filter fun l : LineIndex => l.1 = Manhattan.Axis.horizontal).card = 0 := by
    omega
  rw [Finset.card_eq_zero] at h0
  intro l hl
  cases hax : l.1 with
  | horizontal =>
      exfalso
      have : l ∈ S.filter (fun l : LineIndex => l.1 = Manhattan.Axis.horizontal) :=
        Finset.mem_filter.mpr ⟨hl, hax⟩
      rw [h0] at this
      exact absurd this (Finset.notMem_empty l)
  | vertical => rfl

theorem a7_originLine_zero : Manhattan.originLine 0 = (Manhattan.Axis.horizontal, 0) := rfl
theorem a7_originLine_one : Manhattan.originLine 1 = (Manhattan.Axis.vertical, 0) := rfl

theorem a7_axisShift_one_vertical : axisShift 1 Manhattan.Axis.vertical = 0 := by
  simp [axisShift, finAxis]

theorem a7_axisShift_zero_vertical : axisShift 0 Manhattan.Axis.vertical = 1 := by
  simp [axisShift, finAxis]

/-- Raising a row-supported degree-one vector never produces two columns. -/
theorem inner_verticalPair_walshRaise_axisDegreeOne (p : Fin 2 → ℝ)
    (c : Manhattan.RowLineCoefficient) {U : Finset LineIndex} (hU : U.card = 2)
    (hv : ∀ l ∈ U, l.1 = Manhattan.Axis.vertical) :
    inner ℂ (Manhattan.walshL2 U)
      (walshRaise p (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal c)) = 0 := by
  classical
  rw [inner_walshL2_walshRaise, Fin.sum_univ_two]
  have h0 : Manhattan.originLine 0 ∉ U := by
    intro hmem
    have := hv _ hmem
    rw [a7_originLine_zero] at this
    exact absurd this (by simp)
  rw [if_neg h0, zero_add]
  by_cases h1 : Manhattan.originLine 1 ∈ U
  · rw [if_pos h1]
    have hcard : (U.erase (Manhattan.originLine 1)).card = 1 := by
      rw [Finset.card_erase_of_mem h1, hU]
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
    have haU : a ∈ U := Finset.mem_of_mem_erase (by rw [ha]; exact Finset.mem_singleton_self a)
    have hax : a.1 = Manhattan.Axis.vertical := hv _ haU
    have hafst : a = (Manhattan.Axis.vertical, a.2) := by
      rw [← hax]
    rw [ha, hafst, translateWalshIndex_singleton_pos,
      translateWalshIndex_singleton_neg, a7_axisShift_one_vertical,
      add_zero, sub_zero,
      Manhattan.inner_axisDegreeOneSynthesis_of_ne Manhattan.Axis.horizontal
        Manhattan.Axis.vertical (by simp) a.2 c]
    ring
  · rw [if_neg h1]

theorem card_filter_horizontal_translateWalshIndex (v : Manhattan.Operator.Lattice)
    (S : Finset LineIndex) :
    ((Manhattan.translateWalshIndex v S).filter
        fun l : LineIndex => l.1 = Manhattan.Axis.horizontal).card =
      (S.filter fun l : LineIndex => l.1 = Manhattan.Axis.horizontal).card := by
  classical
  rw [Manhattan.translateWalshIndex, Finset.filter_map, Finset.card_map]
  congr 1

theorem filter_horizontal_eq_empty_of_vertical {U : Finset LineIndex}
    (hv : ∀ l ∈ U, l.1 = Manhattan.Axis.vertical) :
    (U.filter fun l : LineIndex => l.1 = Manhattan.Axis.horizontal) = ∅ := by
  classical
  refine Finset.filter_eq_empty_iff.mpr ?_
  intro l hl
  rw [hv l hl]
  simp

theorem inner_walshL2_type112WalshSynthesis_eq_zero
    (c : ℓ²(Manhattan.Type112Index, ℂ)) {V : Finset LineIndex}
    (hV : (V.filter fun l : LineIndex => l.1 = Manhattan.Axis.horizontal).card ≠ 2) :
    inner ℂ (Manhattan.walshL2 V) (Manhattan.type112WalshSynthesis c) = 0 := by
  classical
  rw [Manhattan.inner_walshL2_type112WalshSynthesis, Manhattan.type112CoefficientAt,
    dif_neg (fun h : Manhattan.IsType112Index V => hV h.2)]

/-- Lowering a type-`(1,1,2)` vector never produces two columns. -/
theorem inner_verticalPair_concreteFiberA_type112 (p : Fin 2 → ℝ)
    (c : ℓ²(Manhattan.Type112Index, ℂ)) {U : Finset LineIndex} (hU : U.card = 2)
    (hv : ∀ l ∈ U, l.1 = Manhattan.Axis.vertical) :
    inner ℂ (Manhattan.walshL2 U)
      (Manhattan.concreteFiberA p (Manhattan.type112WalshSynthesis c)) = 0 := by
  classical
  have hempty := filter_horizontal_eq_empty_of_vertical hv
  have hkey : ∀ (i : Fin 2) (w : Manhattan.Operator.Lattice),
      inner ℂ (Manhattan.walshL2 (Manhattan.translateWalshIndex w
          (insert (Manhattan.originLine i) U)))
        (Manhattan.type112WalshSynthesis c) = 0 := by
    intro i w
    refine inner_walshL2_type112WalshSynthesis_eq_zero c ?_
    rw [card_filter_horizontal_translateWalshIndex]
    fin_cases i
    · rw [Finset.filter_insert, if_pos (by rfl), hempty]
      simp
    · rw [Finset.filter_insert, if_neg (by simp [a7_originLine_one]), hempty]
      simp
  rw [concreteFiberA_eq_walshRaise_sub_walshLower,
    ContinuousLinearMap.sub_apply, inner_sub_right]
  have hraise : inner ℂ (Manhattan.walshL2 U)
      (walshRaise p (Manhattan.type112WalshSynthesis c)) = 0 := by
    refine inner_walshL2_eq_zero_of_mem_walshDegree
      (walshRaise_mem_walshDegree p (Manhattan.type112WalshSynthesis_mem_degree c)) ?_
    rw [hU]; norm_num
  rw [hraise, inner_walshL2_walshLower, Fin.sum_univ_two]
  simp only [hkey]
  by_cases h0 : Manhattan.originLine 0 ∈ U <;> by_cases h1 : Manhattan.originLine 1 ∈ U <;>
    simp [h0, h1]

theorem type11WalshSynthesis_analysis_eq (x : WalshL2) :
    Manhattan.type11WalshSynthesis (Manhattan.type11WalshAnalysis x) =
      walshSectorComponent Manhattan.IsType11Index x := rfl

theorem type12WalshSynthesis_analysis_eq (x : WalshL2) :
    Manhattan.type12WalshSynthesis (Manhattan.type12WalshAnalysis x) =
      walshSectorComponent Manhattan.IsType12Index x := rfl

theorem not_isType12_of_isType11 {S : Finset LineIndex} (h : Manhattan.IsType11Index S) :
    ¬ Manhattan.IsType12Index S := by
  classical
  intro h12
  have hfull : S.filter (fun l : LineIndex => l.1 = Manhattan.Axis.horizontal) = S :=
    Finset.filter_true_of_mem fun l hl => h.2 l hl
  have h2 := h12.2
  rw [hfull, h.1] at h2
  exact absurd h2 (by norm_num)

/-- **The degree-two Walsh sector splits into its two-row and mixed parts.**
There is no two-column sector for a vector whose two-column coefficients all
vanish. -/
theorem walshSectorComponent_two_eq_type11_add_type12 {x : WalshL2}
    (hx : ∀ U : Finset LineIndex, U.card = 2 →
      (∀ l ∈ U, l.1 = Manhattan.Axis.vertical) → inner ℂ (Manhattan.walshL2 U) x = 0) :
    walshSectorComponent (fun S => S.card = 2) x =
      Manhattan.type11WalshSynthesis (Manhattan.type11WalshAnalysis x) +
        Manhattan.type12WalshSynthesis (Manhattan.type12WalshAnalysis x) := by
  classical
  rw [type11WalshSynthesis_analysis_eq, type12WalshSynthesis_analysis_eq]
  refine walshL2_ext ?_
  intro U
  rw [inner_add_right, inner_walshL2_walshSectorComponent,
    inner_walshL2_walshSectorComponent, inner_walshL2_walshSectorComponent]
  by_cases hcard : U.card = 2
  · rw [if_pos hcard]
    rcases isType11_or_isType12_or_vertical hcard with h11 | h12 | hvert
    · rw [if_pos h11, if_neg (not_isType12_of_isType11 h11), add_zero]
    · rw [if_neg (fun h : Manhattan.IsType11Index U => not_isType12_of_isType11 h h12),
        if_pos h12, zero_add]
    · rw [if_neg (fun h : Manhattan.IsType11Index U => by
          obtain ⟨l, hl⟩ := Finset.card_pos.mp (by rw [h.1]; norm_num : 0 < U.card)
          exact absurd ((h.2 l hl).symm.trans (hvert l hl)) (by simp)),
        if_neg (fun h : Manhattan.IsType12Index U => by
          have h2 := h.2
          rw [filter_horizontal_eq_empty_of_vertical hvert] at h2
          simp at h2), add_zero, hx U hcard hvert]
  · rw [if_neg hcard, if_neg (fun h : Manhattan.IsType11Index U => hcard h.1),
      if_neg (fun h : Manhattan.IsType12Index U => hcard h.1), add_zero]

theorem axisDegreeOneSynthesis_mem_walshDegree (i : Manhattan.Axis)
    (c : Manhattan.RowLineCoefficient) :
    Manhattan.axisDegreeOneSynthesis i c ∈ Manhattan.walshDegree 1 := by
  let V : ℤ → ℂ →ₗᵢ[ℂ] WalshL2 := fun k =>
    LinearIsometry.toSpanSingleton ℂ WalshL2
      ((Manhattan.orthonormal_walshL2.comp
        (fun m : ℤ => ({(i, m)} : Finset LineIndex)) (by
          intro m n h
          simpa using h)).1 k)
  let U : Submodule ℂ WalshL2 := ⨆ k, LinearMap.range (V k).toLinearMap
  have hrange : Manhattan.axisDegreeOneSynthesis i c ∈ U.topologicalClosure := by
    have hrange' : Manhattan.axisDegreeOneSynthesis i c ∈
        LinearMap.range
          (Manhattan.orthonormal_walshL2.comp
            (fun k : ℤ => ({(i, k)} : Finset LineIndex)) (by
              intro k l h
              simpa using h)).orthogonalFamily.linearIsometry.toLinearMap := ⟨c, rfl⟩
    rw [OrthogonalFamily.range_linearIsometry] at hrange'
    exact hrange'
  have hU : U ≤ Manhattan.walshDegree 1 := by
    refine iSup_le fun k => ?_
    rintro _ ⟨a, rfl⟩
    change a • Manhattan.walshL2 {(i, k)} ∈ Manhattan.walshDegree 1
    exact (Manhattan.walshDegree 1).smul_mem a (by
      simpa using Manhattan.walshL2_mem_degree {(i, k)})
  exact U.topologicalClosure_minimal hU
    (Submodule.isClosed_topologicalClosure _) hrange

/-- The degree-two two-row coefficients of `A_p(f+k)` come from the raising
part alone once the two-row lowering component vanishes. -/
theorem type11WalshAnalysis_concreteFiberA_add (p : Fin 2 → ℝ)
    (c : Manhattan.RowLineCoefficient) (kc : ℓ²(Manhattan.Type112Index, ℂ))
    (hk : Manhattan.type112DStarTwoRow p kc = 0) :
    Manhattan.type11WalshAnalysis (Manhattan.concreteFiberA p
        (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal c +
          Manhattan.type112WalshSynthesis kc)) =
      Manhattan.type11WalshAnalysis
        (walshRaise p (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal c)) := by
  classical
  apply lp.ext
  funext T
  have hk' : Manhattan.type112DStarTwoRow p kc T = 0 := by rw [hk]; rfl
  rw [Manhattan.type112DStarTwoRow, Manhattan.type11WalshAnalysis,
    Manhattan.walshSectorAnalysis_apply, inner_neg_right, neg_eq_zero] at hk'
  rw [Manhattan.type11WalshAnalysis, Manhattan.walshSectorAnalysis_apply,
    Manhattan.type11WalshAnalysis, Manhattan.walshSectorAnalysis_apply,
    map_add, inner_add_right, hk', add_zero,
    concreteFiberA_eq_walshRaise_sub_walshLower, ContinuousLinearMap.sub_apply,
    inner_sub_right]
  have hlow : inner ℂ (Manhattan.walshL2 T.1)
      (walshLower p (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal c)) = 0 := by
    refine inner_walshL2_eq_zero_of_mem_walshDegree
      (walshLower_mem_walshDegree p
        (axisDegreeOneSynthesis_mem_walshDegree Manhattan.Axis.horizontal c)) ?_
    rw [T.2.1]
    norm_num
  rw [hlow, sub_zero]

/-- The degree-two mixed coefficients of `A_p(f+k)` are the mixed raising
coefficients of `f` minus the mixed lowering coefficients of `k`. -/
theorem type12WalshAnalysis_concreteFiberA_add (p : Fin 2 → ℝ)
    (c : Manhattan.RowLineCoefficient) (kc : ℓ²(Manhattan.Type112Index, ℂ)) :
    Manhattan.type12WalshAnalysis (Manhattan.concreteFiberA p
        (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal c +
          Manhattan.type112WalshSynthesis kc)) =
      Manhattan.type12WalshAnalysis
          (walshRaise p (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal c)) -
        Manhattan.type112DStarMixed p kc := by
  classical
  apply lp.ext
  funext T
  have hmixed : Manhattan.type112DStarMixed p kc T =
      -inner ℂ (Manhattan.walshL2 T.1)
        (Manhattan.concreteFiberA p (Manhattan.type112WalshSynthesis kc)) := by
    rw [Manhattan.type112DStarMixed, Manhattan.type12WalshAnalysis,
      Manhattan.walshSectorAnalysis_apply, inner_neg_right]
  have hsub : (Manhattan.type12WalshAnalysis
      (walshRaise p (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal c)) -
        Manhattan.type112DStarMixed p kc) T =
      Manhattan.type12WalshAnalysis
        (walshRaise p (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal c)) T -
      Manhattan.type112DStarMixed p kc T := rfl
  rw [hsub, hmixed, Manhattan.type12WalshAnalysis, Manhattan.walshSectorAnalysis_apply,
    Manhattan.type12WalshAnalysis, Manhattan.walshSectorAnalysis_apply,
    map_add, inner_add_right, sub_neg_eq_add]
  congr 1
  rw [concreteFiberA_eq_walshRaise_sub_walshLower, ContinuousLinearMap.sub_apply,
    inner_sub_right]
  have hlow : inner ℂ (Manhattan.walshL2 T.1)
      (walshLower p (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal c)) = 0 := by
    refine inner_walshL2_eq_zero_of_mem_walshDegree
      (walshLower_mem_walshDegree p
        (axisDegreeOneSynthesis_mem_walshDegree Manhattan.Axis.horizontal c)) ?_
    rw [T.2.1]
    norm_num
  rw [hlow, sub_zero]

theorem inner_verticalPair_concreteFiberA_add (p : Fin 2 → ℝ)
    (c : Manhattan.RowLineCoefficient) (kc : ℓ²(Manhattan.Type112Index, ℂ))
    {U : Finset LineIndex} (hU : U.card = 2)
    (hv : ∀ l ∈ U, l.1 = Manhattan.Axis.vertical) :
    inner ℂ (Manhattan.walshL2 U)
      (Manhattan.concreteFiberA p
        (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal c +
          Manhattan.type112WalshSynthesis kc)) = 0 := by
  classical
  rw [map_add, inner_add_right, inner_verticalPair_concreteFiberA_type112 p kc hU hv,
    add_zero, concreteFiberA_eq_walshRaise_sub_walshLower, ContinuousLinearMap.sub_apply,
    inner_sub_right, inner_verticalPair_walshRaise_axisDegreeOne p c hU hv]
  have hlow : inner ℂ (Manhattan.walshL2 U)
      (walshLower p (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal c)) = 0 := by
    refine inner_walshL2_eq_zero_of_mem_walshDegree
      (walshLower_mem_walshDegree p
        (axisDegreeOneSynthesis_mem_walshDegree Manhattan.Axis.horizontal c)) ?_
    rw [hU]
    norm_num
  rw [hlow, sub_zero]

/-- **The degree-two Walsh sector of `A_p(f+k)`.**  There is no two-column
part; the two-row part comes from `D₁f` alone once the two-row lowering
component of `k` vanishes; and the mixed part is `(D₁f)₁₂-(D₂*k)₁₂`. -/
theorem walshSectorComponent_two_concreteFiberA_eq (p : Fin 2 → ℝ)
    (c : Manhattan.RowLineCoefficient) (kc : ℓ²(Manhattan.Type112Index, ℂ))
    (hk : Manhattan.type112DStarTwoRow p kc = 0) :
    walshSectorComponent (fun S => S.card = 2)
        (Manhattan.concreteFiberA p
          (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal c +
            Manhattan.type112WalshSynthesis kc)) =
      Manhattan.type11WalshSynthesis (Manhattan.type11WalshAnalysis
          (walshRaise p (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal c))) +
        Manhattan.type12WalshSynthesis
          (Manhattan.type12WalshAnalysis
              (walshRaise p (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal c)) -
            Manhattan.type112DStarMixed p kc) := by
  rw [walshSectorComponent_two_eq_type11_add_type12
      (fun U hU hv => inner_verticalPair_concreteFiberA_add p c kc hU hv),
    type11WalshAnalysis_concreteFiberA_add p c kc hk,
    type12WalshAnalysis_concreteFiberA_add p c kc]

theorem correctedRowVector_eq_axisDegreeOneSynthesis (d : LowDegreeCompetitorData) :
    correctedRowVector d =
      Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal
        (fourierBasis.repr d.rowFrequency) := rfl

/-- **Summand 3 splits into its two-row and mixed halves.** -/
theorem hMinusEnergy_sectorTwo_le {lam : ℝ} (hlam : 0 < lam) (p : Fin 2 → ℝ) (b : ℝ)
    (c : Manhattan.RowLineCoefficient) (kc : ℓ²(Manhattan.Type112Index, ℂ))
    (hk : Manhattan.type112DStarTwoRow p kc = 0) :
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hlam
        (walshSectorComponent (fun S => S.card = 2)
          (unnormalizedResidual p b
            (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal c)
            (Manhattan.type112WalshSynthesis kc))) ≤
      2 * (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hlam
          (Manhattan.type11WalshSynthesis (Manhattan.type11WalshAnalysis
            (walshRaise p (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal c)))) +
        2 * (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hlam
          (Manhattan.type12WalshSynthesis
            (Manhattan.type12WalshAnalysis
                (walshRaise p (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal c)) -
              Manhattan.type112DStarMixed p kc)) := by
  rw [walshSectorComponent_two_unnormalizedResidual, hMinusEnergy_neg,
    walshSectorComponent_two_concreteFiberA_eq p c kc hk]
  exact hMinusEnergy_add_le _ hlam _ _

open Manhattan.Estimates in
/-- **The reduction of summand 3 of (22).**  `SummandThreeBound` follows from
one bound on the two-row degree-two sector of `D₁f_p` and one bound on the
mixed degree-two sector of `D₁f_p-D₂*k_p`. -/
theorem summandThreeBound_of_sector_bounds {C11 C12 : ℝ}
    (h11 : ∀ (q : Estimates.Parameters), q.K = correctedCompetitorK →
        q.rho = correctedCompetitorRho → q.lambda ≤ 1 →
      ∀ (hlambda : 0 < q.lambda) (p : Fin 2 → ℝ), p 0 ∈ Estimates.torus →
        p 1 ∈ Estimates.torus → |p 1| ≤ |p 0| → 0 < |p 0| →
        q.logThreshold < q.scaleLog |p 0| →
      ∀ (hcert : Estimates.LemmaFourTwoIntegralCertificate q (p 0) (p 1))
        (hnormalization : Estimates.degreeOneNormalization q (p 0) ≠ 0),
        (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hlambda
            (Manhattan.type11WalshSynthesis (Manhattan.type11WalshAnalysis
              (walshRaise p (correctedRowVector
                (correctedLowDegreeData hlambda p hcert hnormalization))))) ≤
          C11 * Real.sqrt (q.scaleLog |p 0|))
    (h12 : ∀ (q : Estimates.Parameters), q.K = correctedCompetitorK →
        q.rho = correctedCompetitorRho → q.lambda ≤ 1 →
      ∀ (hlambda : 0 < q.lambda) (p : Fin 2 → ℝ), p 0 ∈ Estimates.torus →
        p 1 ∈ Estimates.torus → |p 1| ≤ |p 0| → 0 < |p 0| →
        q.logThreshold < q.scaleLog |p 0| →
      ∀ (hcert : Estimates.LemmaFourTwoIntegralCertificate q (p 0) (p 1))
        (hnormalization : Estimates.degreeOneNormalization q (p 0) ≠ 0),
        (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hlambda
            (Manhattan.type12WalshSynthesis
              (Manhattan.type12WalshAnalysis
                  (walshRaise p (correctedRowVector
                    (correctedLowDegreeData hlambda p hcert hnormalization))) -
                Manhattan.type112DStarMixed p
                  (correctedLowDegreeData hlambda p hcert hnormalization).mixedCoefficient)) ≤
          C12 * Real.sqrt (q.scaleLog |p 0|)) :
    SummandThreeBound (2 * C11 + 2 * C12) := by
  intro lambda hlambda hlambdaOne p hp₀ hp₁ horder hpositive
  let q : Estimates.Parameters :=
    ⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩
  change q.logThreshold < q.scaleLog |p 0| → _
  intro hlog hcert hnormalization
  have hk : Manhattan.type112DStarTwoRow p
      (correctedLowDegreeData hlambda p hcert hnormalization).mixedCoefficient = 0 :=
    type112DStarTwoRow_correctedLowDegreeData hlambda p hcert hnormalization
  have hsplit := hMinusEnergy_sectorTwo_le hlambda p
    (correctedLowDegreeData hlambda p hcert hnormalization).normalization
    (fourierBasis.repr (correctedLowDegreeData hlambda p hcert hnormalization).rowFrequency)
    (correctedLowDegreeData hlambda p hcert hnormalization).mixedCoefficient hk
  have hA := h11 q rfl rfl hlambdaOne hlambda p hp₀ hp₁ horder hpositive hlog hcert
    hnormalization
  have hB := h12 q rfl rfl hlambdaOne hlambda p hp₀ hp₁ horder hpositive hlog hcert
    hnormalization
  rw [correctedRowVector_eq_axisDegreeOneSynthesis] at hA hB
  refine hsplit.trans ?_
  show _ ≤ (2 * C11 + 2 * C12) * Real.sqrt (q.scaleLog |p 0|)
  linarith [hA, hB]

theorem a7_axisShift_zero_horizontal : axisShift 0 Manhattan.Axis.horizontal = 0 := by
  simp [axisShift, finAxis]

theorem a7_axisShift_one_horizontal : axisShift 1 Manhattan.Axis.horizontal = 1 := by
  simp [axisShift, finAxis]

/-- **The mixed degree-two coefficient of `D₁f`.**  It is carried entirely by
the origin column: the paper's `w(r,β)=i sin(r)f(r)` does not depend on `β`. -/
theorem inner_mixedPair_walshRaise_axisDegreeOne (p : Fin 2 → ℝ)
    (c : Manhattan.RowLineCoefficient) (m n : ℤ) :
    inner ℂ (Manhattan.walshL2 (mixedPairFinset (m, n)))
        (walshRaise p (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal c)) =
      if n = 0 then
        (2 : ℂ)⁻¹ *
          (Complex.exp (Complex.I * p 1) * c (m - 1) -
            Complex.exp (-Complex.I * p 1) * c (m + 1))
      else 0 := by
  classical
  rw [inner_walshL2_walshRaise, Fin.sum_univ_two]
  have hrow : (if Manhattan.originLine 0 ∈ mixedPairFinset (m, n) then
        (2 : ℂ)⁻¹ *
          (Complex.exp (Complex.I * p 0) *
              inner ℂ (Manhattan.walshL2 (Manhattan.translateWalshIndex
                (-Manhattan.Operator.axisVector 0)
                ((mixedPairFinset (m, n)).erase (Manhattan.originLine 0))))
                (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal c) -
            Complex.exp (-Complex.I * p 0) *
              inner ℂ (Manhattan.walshL2 (Manhattan.translateWalshIndex
                (Manhattan.Operator.axisVector 0)
                ((mixedPairFinset (m, n)).erase (Manhattan.originLine 0))))
                (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal c))
      else 0) = 0 := by
    by_cases h : Manhattan.originLine 0 ∈ mixedPairFinset (m, n)
    · rw [if_pos h]
      have hm : m = 0 := by
        rw [a7_originLine_zero, mixedPairFinset] at h
        simp only [Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with h | h
        · exact (congrArg Prod.snd h).symm
        · exact absurd (congrArg Prod.fst h) (by simp)
      subst hm
      have herase : (mixedPairFinset ((0 : ℤ), n)).erase (Manhattan.originLine 0) =
          {(Manhattan.Axis.vertical, n)} := by
        show (insert ((Manhattan.Axis.horizontal, (0 : ℤ)) : LineIndex)
            ({(Manhattan.Axis.vertical, n)} : Finset LineIndex)).erase
            ((Manhattan.Axis.horizontal, (0 : ℤ)) : LineIndex) = _
        exact Finset.erase_insert (by simp)
      rw [herase, translateWalshIndex_singleton_pos, translateWalshIndex_singleton_neg,
        Manhattan.inner_axisDegreeOneSynthesis_of_ne Manhattan.Axis.horizontal
          Manhattan.Axis.vertical (by simp) _ c,
        Manhattan.inner_axisDegreeOneSynthesis_of_ne Manhattan.Axis.horizontal
          Manhattan.Axis.vertical (by simp) _ c]
      ring
    · rw [if_neg h]
  rw [hrow, zero_add]
  by_cases hn : n = 0
  · subst hn
    have hmem : Manhattan.originLine 1 ∈ mixedPairFinset (m, (0 : ℤ)) := by
      rw [a7_originLine_one, mixedPairFinset]
      simp
    have herase : (mixedPairFinset (m, (0 : ℤ))).erase (Manhattan.originLine 1) =
        {(Manhattan.Axis.horizontal, m)} := by
      have hcomm : mixedPairFinset (m, (0 : ℤ)) =
          insert ((Manhattan.Axis.vertical, (0 : ℤ)) : LineIndex)
            ({(Manhattan.Axis.horizontal, m)} : Finset LineIndex) :=
        Finset.pair_comm _ _
      rw [a7_originLine_one, hcomm]
      exact Finset.erase_insert (by simp)
    rw [if_pos hmem, herase, translateWalshIndex_singleton_pos,
      translateWalshIndex_singleton_neg, a7_axisShift_one_horizontal,
      Manhattan.inner_axisDegreeOneSynthesis, Manhattan.inner_axisDegreeOneSynthesis,
      if_pos rfl]
  · have hmem : Manhattan.originLine 1 ∉ mixedPairFinset (m, n) := by
      rw [a7_originLine_one, mixedPairFinset]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨fun hcon => absurd (congrArg Prod.fst hcon) (by simp), fun hcon => ?_⟩
      exact hn (congrArg Prod.snd hcon).symm
    rw [if_neg hmem, if_neg hn]

/-- **The two-row degree-two coefficient of `D₁f`.**  In the Finset
convention the symmetrization `f(r)+f(r')` of (D2a) is replaced by the single
term whose omitted line is the origin row. -/
theorem inner_rowPair_walshRaise_axisDegreeOne (p : Fin 2 → ℝ)
    (c : Manhattan.RowLineCoefficient) {m m' : ℤ} (hne : m ≠ m') :
    inner ℂ (Manhattan.walshL2 (rowPairFinset (m, m')))
        (walshRaise p (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal c)) =
      (if m = 0 then Complex.I * (Real.sin (p 0) : ℂ) * c m' else 0) +
        (if m' = 0 then Complex.I * (Real.sin (p 0) : ℂ) * c m else 0) := by
  classical
  rw [inner_walshL2_walshRaise, Fin.sum_univ_two]
  have hcol : Manhattan.originLine 1 ∉ rowPairFinset (m, m') := by
    rw [a7_originLine_one, rowPairFinset]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun hcon => absurd (congrArg Prod.fst hcon) (by simp),
      fun hcon => absurd (congrArg Prod.fst hcon) (by simp)⟩
  rw [if_neg hcol, add_zero]
  by_cases hm : m = 0
  · subst hm
    have hm' : m' ≠ 0 := fun h => hne (by rw [h])
    have hmem : Manhattan.originLine 0 ∈ rowPairFinset ((0 : ℤ), m') := by
      rw [a7_originLine_zero, rowPairFinset]
      simp
    have herase : (rowPairFinset ((0 : ℤ), m')).erase (Manhattan.originLine 0) =
        {(Manhattan.Axis.horizontal, m')} := by
      show (insert ((Manhattan.Axis.horizontal, (0 : ℤ)) : LineIndex)
          ({(Manhattan.Axis.horizontal, m')} : Finset LineIndex)).erase
          ((Manhattan.Axis.horizontal, (0 : ℤ)) : LineIndex) = _
      exact Finset.erase_insert (by simp [Ne.symm hm'])
    rw [if_pos hmem, herase, translateWalshIndex_singleton_pos,
      translateWalshIndex_singleton_neg, a7_axisShift_zero_horizontal,
      add_zero, sub_zero, Manhattan.inner_axisDegreeOneSynthesis, if_pos rfl,
      if_neg hm']
    have hsin := Manhattan.half_exp_I_sub_exp_neg_I (p 0)
    rw [add_zero]
    linear_combination (c m') * hsin
  · by_cases hm' : m' = 0
    · subst hm'
      have hmem : Manhattan.originLine 0 ∈ rowPairFinset (m, (0 : ℤ)) := by
        rw [a7_originLine_zero, rowPairFinset]
        simp
      have herase : (rowPairFinset (m, (0 : ℤ))).erase (Manhattan.originLine 0) =
          {(Manhattan.Axis.horizontal, m)} := by
        have hcomm : rowPairFinset (m, (0 : ℤ)) =
            insert ((Manhattan.Axis.horizontal, (0 : ℤ)) : LineIndex)
              ({(Manhattan.Axis.horizontal, m)} : Finset LineIndex) :=
          Finset.pair_comm _ _
        rw [a7_originLine_zero, hcomm]
        exact Finset.erase_insert (by simp [Ne.symm hm])
      rw [if_pos hmem, herase, translateWalshIndex_singleton_pos,
        translateWalshIndex_singleton_neg, a7_axisShift_zero_horizontal,
        add_zero, sub_zero, Manhattan.inner_axisDegreeOneSynthesis, if_neg hm,
        if_pos rfl, zero_add]
      have hsin := Manhattan.half_exp_I_sub_exp_neg_I (p 0)
      linear_combination (c m) * hsin
    · have hmem : Manhattan.originLine 0 ∉ rowPairFinset (m, m') := by
        rw [a7_originLine_zero, rowPairFinset]
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun hcon => hm (congrArg Prod.snd hcon).symm,
          fun hcon => hm' (congrArg Prod.snd hcon).symm⟩
      rw [if_neg hmem, if_neg hm, if_neg hm', add_zero]

/-- The two-row degree-two Walsh coefficient of the concrete residual. -/
theorem type11WalshAnalysis_walshRaise_rowPair (p : Fin 2 → ℝ)
    (c : Manhattan.RowLineCoefficient) {m m' : ℤ} (hne : m ≠ m') :
    Manhattan.type11WalshAnalysis
        (walshRaise p (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal c))
        ⟨rowPairFinset (m, m'), isType11Index_rowPairFinset hne⟩ =
      (if m = 0 then Complex.I * (Real.sin (p 0) : ℂ) * c m' else 0) +
        (if m' = 0 then Complex.I * (Real.sin (p 0) : ℂ) * c m else 0) := by
  rw [Manhattan.type11WalshAnalysis, Manhattan.walshSectorAnalysis_apply]
  exact inner_rowPair_walshRaise_axisDegreeOne p c hne

/-- **Equation (onI) at the Walsh level.**  The mixed degree-two coefficient
of the concrete residual `D₁f_p-D₂*k_p` at the line pair `(m,n)`: the raising
half is carried by the origin column alone, and the lowering half reads the
degree-three coefficient at the two column neighbours of `n` with the second
row index pinned to the origin.
-/
theorem type12WalshAnalysis_sub_type112DStarMixed_apply (p : Fin 2 → ℝ)
    (c : Manhattan.RowLineCoefficient) (kc : ℓ²(Manhattan.Type112Index, ℂ)) (m n : ℤ) :
    (Manhattan.type12WalshAnalysis
          (walshRaise p (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal c)) -
        Manhattan.type112DStarMixed p kc)
        ⟨mixedPairFinset (m, n), isType12Index_mixedPairFinset m n⟩ =
      (if n = 0 then
        (2 : ℂ)⁻¹ *
          (Complex.exp (Complex.I * p 1) * c (m - 1) -
            Complex.exp (-Complex.I * p 1) * c (m + 1))
      else 0) -
        (((2 : ℂ)⁻¹ * Complex.exp (-Complex.I * p 0)) *
            Manhattan.type112CoefficientAt kc (tripleToFinset (m, 0, n + 1)) -
          ((2 : ℂ)⁻¹ * Complex.exp (Complex.I * p 0)) *
            Manhattan.type112CoefficientAt kc (tripleToFinset (m, 0, n - 1))) := by
  have hsub : (Manhattan.type12WalshAnalysis
        (walshRaise p (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal c)) -
      Manhattan.type112DStarMixed p kc)
        ⟨mixedPairFinset (m, n), isType12Index_mixedPairFinset m n⟩ =
      Manhattan.type12WalshAnalysis
          (walshRaise p (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal c))
          ⟨mixedPairFinset (m, n), isType12Index_mixedPairFinset m n⟩ -
        Manhattan.type112DStarMixed p kc
          ⟨mixedPairFinset (m, n), isType12Index_mixedPairFinset m n⟩ := rfl
  rw [hsub, Manhattan.type12WalshAnalysis, Manhattan.walshSectorAnalysis_apply,
    inner_mixedPair_walshRaise_axisDegreeOne p c m n, type112DStarMixed_eq p kc m n]

theorem l2Extend_apply {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] (f : ι → κ)
    (hf : Function.Injective f) (a : ℓ²(ι, ℂ)) (i : ι) :
    l2Extend f hf a (f i) = a i := by
  have h1 : ∀ x : ℓ²(κ, ℂ), inner ℂ (lp.single 2 (f i) (1 : ℂ)) x = x (f i) := by
    intro x
    rw [lp.inner_single_left]
    simp
  have h2 : ∀ y : ℓ²(ι, ℂ), inner ℂ (lp.single 2 i (1 : ℂ)) y = y i := by
    intro y
    rw [lp.inner_single_left]
    simp
  rw [← h1, ← l2Extend_single f hf i (1 : ℂ), (l2Extend f hf).inner_map_map, h2]

theorem l2Extend_apply_eq_zero {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] (f : ι → κ)
    (hf : Function.Injective f) (a : ℓ²(ι, ℂ)) {k : κ} (hk : ∀ i, f i ≠ k) :
    l2Extend f hf a k = 0 := by
  have h1 : ∀ x : ℓ²(κ, ℂ), inner ℂ (lp.single 2 k (1 : ℂ)) x = x k := by
    intro x
    rw [lp.inner_single_left]
    simp
  rw [← h1]
  refine l2_ext'
    ((innerSL ℂ (lp.single 2 k (1 : ℂ))).comp (l2Extend f hf).toContinuousLinearMap) 0 ?_ a
  intro i
  show inner ℂ (lp.single 2 k (1 : ℂ)) (l2Extend f hf (lp.single 2 i (1 : ℂ))) = 0
  rw [l2Extend_single, lp.inner_single_left]
  simp [hk i]

/-- **The Fourier identification of a mixed degree-two frequency function.**
An `L²` function of the two line frequencies whose two-dimensional Fourier
coefficients are the mixed Walsh coefficients, and which vanishes off the
mixed carrier, *is* the frequency function of that Walsh vector.  This is the
hypothesis `hG` of `hMinusEnergy_type12WalshSynthesis_torusIntegral`. -/
theorem type12FreqFun_eq_of_mFourierCoeff (cc : ℓ²(Manhattan.Type12Index, ℂ))
    (G : Lp ℂ 2 (LineTorusMeasure 2))
    (hon : ∀ S : Manhattan.Type12Index,
      UnitAddTorus.mFourierCoeff ((G : UnitAddTorus (Fin 2) → ℂ)) (type12RawIndex S) = cc S)
    (hoff : ∀ n : Fin 2 → ℤ, (∀ S : Manhattan.Type12Index, type12RawIndex S ≠ n) →
      UnitAddTorus.mFourierCoeff ((G : UnitAddTorus (Fin 2) → ℂ)) n = 0) :
    type12FreqFun cc = G := by
  classical
  have hrepr : (UnitAddTorus.mFourierBasis (d := Fin 2)).repr G = type12RawExtend cc := by
    apply lp.ext
    funext n
    rw [UnitAddTorus.mFourierBasis_repr]
    by_cases h : ∃ S : Manhattan.Type12Index, type12RawIndex S = n
    · obtain ⟨S, rfl⟩ := h
      rw [hon S, type12RawExtend, l2Extend_apply]
    · push_neg at h
      rw [hoff n h, type12RawExtend, l2Extend_apply_eq_zero _ _ _ h]
  show (UnitAddTorus.mFourierBasis (d := Fin 2)).repr.symm (type12RawExtend cc) = G
  rw [← hrepr, LinearIsometryEquiv.symm_apply_apply]

/-- The same identification for the two-row degree-two sector.
-/
theorem type11FreqFun_eq_of_mFourierCoeff (cc : ℓ²(Manhattan.Type11Index, ℂ))
    (G : Lp ℂ 2 (LineTorusMeasure 2))
    (hon : ∀ S : Manhattan.Type11Index,
      UnitAddTorus.mFourierCoeff ((G : UnitAddTorus (Fin 2) → ℂ)) (type11RawIndex S) = cc S)
    (hoff : ∀ n : Fin 2 → ℤ, (∀ S : Manhattan.Type11Index, type11RawIndex S ≠ n) →
      UnitAddTorus.mFourierCoeff ((G : UnitAddTorus (Fin 2) → ℂ)) n = 0) :
    type11FreqFun cc = G := by
  classical
  have hrepr : (UnitAddTorus.mFourierBasis (d := Fin 2)).repr G = type11RawExtend cc := by
    apply lp.ext
    funext n
    rw [UnitAddTorus.mFourierBasis_repr]
    by_cases h : ∃ S : Manhattan.Type11Index, type11RawIndex S = n
    · obtain ⟨S, rfl⟩ := h
      rw [hon S, type11RawExtend, l2Extend_apply]
    · push_neg at h
      rw [hoff n h, type11RawExtend, l2Extend_apply_eq_zero _ _ _ h]
  show (UnitAddTorus.mFourierBasis (d := Fin 2)).repr.symm (type11RawExtend cc) = G
  rw [← hrepr, LinearIsometryEquiv.symm_apply_apply]

end DegreeTwoSectorSplit

end

end Manhattan.Glue
