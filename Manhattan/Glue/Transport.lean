import Manhattan.Glue.ConcreteMultiplier
import Manhattan.Glue.CubicDischarge

/-!
# The Plancherel--multiplier transport for the type-`(1,1,2)` sector

The type-`(1,1,2)` Walsh synthesis of `Manhattan/Walsh/Correction.lean` is
identified with degree-three line-frequency picture under the
line-index Fourier transform (20).  The sorted enumeration of a type-`(1,1,2)`
Finset index is the two horizontal lines in increasing order followed by the
vertical line, so the whole sector sits in the single axis pattern
`(horizontal, horizontal, vertical)` and its frequency side is one honest `L²`
function of the three line frequencies.  Consequently the degree-three `H` and
`H⁻¹` quadratic forms of a type-`(1,1,2)` coefficient are the explicit weighted
integrals `∫ (λ + θ(P)) |k̂|²` and `∫ (λ + θ(P))⁻¹ |k̂|²`.

Paper: `manuscript.tex:719-751` (equations (19), (20) and (Hsym)),
`manuscript.tex:812-814` (the shifted frequency variables `r`, `r'`, `β`),
`manuscript.tex:1045-1052` (the corrected coefficient).
-/

noncomputable section

open MeasureTheory UnitAddTorus

namespace Manhattan.Glue

/-! ### Extension by zero along an injection -/

private theorem orthonormal_l2Single' (ι : Type*) [DecidableEq ι] :
    Orthonormal ℂ (fun i : ι => lp.single 2 i (1 : ℂ)) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [lp.inner_single_left]
  by_cases h : i = j
  · subst h; simp
  · simp [lp.single_apply, h]

/-- Extension by zero along an injection, as a linear isometry of `l²` spaces. -/
def l2Extend {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] (f : ι → κ)
    (hf : Function.Injective f) : ℓ²(ι, ℂ) →ₗᵢ[ℂ] ℓ²(κ, ℂ) :=
  ((orthonormal_l2Single' κ).comp f hf).orthogonalFamily.linearIsometry

theorem lp_single_smul {ι : Type*} [DecidableEq ι] (i : ι) (a : ℂ) :
    a • (lp.single 2 i (1 : ℂ) : ℓ²(ι, ℂ)) = lp.single 2 i a := by
  rw [← lp.single_smul]
  simp

@[simp] theorem l2Extend_single {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (f : ι → κ) (hf : Function.Injective f) (i : ι) (a : ℂ) :
    l2Extend f hf (lp.single 2 i a) = lp.single 2 (f i) a := by
  rw [l2Extend, OrthogonalFamily.linearIsometry_apply_single]
  exact lp_single_smul _ _

private def l2Basis' (ι : Type*) : HilbertBasis ι ℂ (ℓ²(ι, ℂ)) :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)

private theorem l2Basis'_apply {ι : Type*} [DecidableEq ι] (i : ι) :
    l2Basis' ι i = lp.single 2 i (1 : ℂ) :=
  (HilbertBasis.repr_symm_single (l2Basis' ι) i).symm

theorem l2_ext' {ι : Type*} [DecidableEq ι] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T U : ℓ²(ι, ℂ) →L[ℂ] E)
    (h : ∀ i : ι, T (lp.single 2 i (1 : ℂ)) = U (lp.single 2 i (1 : ℂ)))
    (c : ℓ²(ι, ℂ)) : T c = U c := by
  have hTU : T = U := by
    refine ContinuousLinearMap.ext_on (s := Set.range (l2Basis' ι)) ?_ ?_
    · rw [Submodule.dense_iff_topologicalClosure_eq_top]
      exact (l2Basis' ι).dense_span
    rintro _ ⟨i, rfl⟩
    rw [l2Basis'_apply]
    exact h i
  rw [hTU]

/-! ### The sorted enumeration of a type-`(1,1,2)` index -/

section Enumeration

attribute [local instance] lineOrder

/-- The degree-three Walsh index underlying a type-`(1,1,2)` index. -/
def type112Degree (S : Manhattan.Type112Index) : WalshDegreeIndex 3 := ⟨S.1, S.2.1⟩

theorem type112Degree_injective : Function.Injective type112Degree := by
  intro S T h
  exact Subtype.ext (congrArg (fun U : WalshDegreeIndex 3 => U.1) h)

/-- The axis pattern of the sorted enumeration of a type-`(1,1,2)` index:
two horizontal lines and then the vertical one. -/
def type112Pattern : Fin 3 → Axis := ![Axis.horizontal, Axis.horizontal, Axis.vertical]

theorem type112RawIndex_lt (S : Manhattan.Type112Index) :
    Manhattan.type112RawIndex S 0 < Manhattan.type112RawIndex S 1 :=
  (Manhattan.orderedType112Equiv.symm S).2

theorem type112Lines_eq (S : Manhattan.Type112Index) :
    ({(Axis.horizontal, Manhattan.type112RawIndex S 0),
      (Axis.horizontal, Manhattan.type112RawIndex S 1),
      (Axis.vertical, Manhattan.type112RawIndex S 2)} : Finset LineIndex) = S.1 :=
  congrArg Subtype.val (Manhattan.orderedType112Equiv.apply_symm_apply S)

/-- The sorted enumeration of a type-`(1,1,2)` index is the two horizontal
lines in increasing order followed by the vertical line. -/
theorem degreeEnum_type112Degree (S : Manhattan.Type112Index) :
    degreeEnum (type112Degree S) =
      fun a => (type112Pattern a, Manhattan.type112RawIndex S a) := by
  symm
  apply Finset.orderEmbOfFin_unique
  · intro x
    have hmem : ((type112Pattern x, Manhattan.type112RawIndex S x) : LineIndex) ∈
        ({(Axis.horizontal, Manhattan.type112RawIndex S 0),
          (Axis.horizontal, Manhattan.type112RawIndex S 1),
          (Axis.vertical, Manhattan.type112RawIndex S 2)} : Finset LineIndex) := by
      fin_cases x <;> simp [type112Pattern]
    rw [type112Lines_eq] at hmem
    exact hmem
  · rw [Fin.strictMono_iff_lt_succ]
    intro i
    fin_cases i
    · show ((Axis.horizontal, Manhattan.type112RawIndex S 0) : LineIndex) <
        (Axis.horizontal, Manhattan.type112RawIndex S 1)
      exact lineIndex_lt_of_coord_lt (type112RawIndex_lt S)
    · show ((Axis.horizontal, Manhattan.type112RawIndex S 1) : LineIndex) <
        (Axis.vertical, Manhattan.type112RawIndex S 2)
      exact horizontal_lt_vertical _ _

theorem tuplePattern_degreeEnum_type112 (S : Manhattan.Type112Index) :
    tuplePattern (degreeEnum (type112Degree S)) = type112Pattern := by
  rw [degreeEnum_type112Degree]; rfl

theorem tupleCoord_degreeEnum_type112 (S : Manhattan.Type112Index) :
    tupleCoord (degreeEnum (type112Degree S)) = Manhattan.type112RawIndex S := by
  rw [degreeEnum_type112Degree]; rfl

end Enumeration

end Manhattan.Glue

namespace Manhattan.Glue

noncomputable section

open MeasureTheory UnitAddTorus

/-! ### The type-`(1,1,2)` sector inside degree three -/

/-- Extension by zero from the type-`(1,1,2)` carrier to degree three. -/
def type112Extend : ℓ²(Manhattan.Type112Index, ℂ) →ₗᵢ[ℂ] DegreeCoefficient 3 :=
  l2Extend type112Degree type112Degree_injective

/-- Extension by zero from the type-`(1,1,2)` carrier to the raw ordered
triples of line coordinates. -/
def rawExtend :
    ℓ²(Manhattan.Type112Index, ℂ) →ₗᵢ[ℂ] ℓ²(Manhattan.RawType112Index, ℂ) :=
  l2Extend Manhattan.type112RawIndex Manhattan.type112RawIndex_injective

theorem type112WalshSynthesis_eq_homogeneous (c : ℓ²(Manhattan.Type112Index, ℂ)) :
    Manhattan.type112WalshSynthesis c =
      homogeneousWalshSynthesis 3 (type112Extend c) := by
  refine l2_ext' Manhattan.type112WalshSynthesis.toContinuousLinearMap
    ((homogeneousWalshSynthesis 3).toContinuousLinearMap.comp
      type112Extend.toContinuousLinearMap) ?_ c
  intro S
  change Manhattan.type112WalshSynthesis (lp.single 2 S (1 : ℂ)) =
    homogeneousWalshSynthesis 3 (type112Extend (lp.single 2 S (1 : ℂ)))
  rw [Manhattan.type112WalshSynthesis_single, type112Extend, l2Extend_single,
    homogeneousWalshSynthesis_single]
  rfl

theorem two_pos_ennreal : (0 : ENNReal) < 2 := by norm_num

/-- The constant family of `L²` spaces indexed by axis patterns. -/
abbrev lineFreqFamily : (Fin 3 → Axis) → Type :=
  fun _ => Lp ℂ 2 (LineTorusMeasure 3)

/-- `lp.single` in the axis-pattern coordinate, as a linear isometry. -/
def freqSingle (σ : Fin 3 → Axis) :
    Lp ℂ 2 (LineTorusMeasure 3) →ₗᵢ[ℂ] LineFreqL2 3 where
  toLinearMap := lp.lsingle (E := lineFreqFamily) 2 σ
  norm_map' f := lp.norm_single (E := lineFreqFamily) two_pos_ennreal σ f

@[simp] theorem freqSingle_apply (σ : Fin 3 → Axis) (f : Lp ℂ 2 (LineTorusMeasure 3)) :
    freqSingle σ f = lp.single (E := lineFreqFamily) 2 σ f := rfl

/-- The `L²` function of the three line frequencies attached to a type-`(1,1,2)`
coefficient: its multivariate Fourier coefficients are the coefficient itself,
extended by zero off the strictly ordered row pairs. -/
def type112FreqFun :
    ℓ²(Manhattan.Type112Index, ℂ) →ₗᵢ[ℂ] Lp ℂ 2 (LineTorusMeasure 3) :=
  (UnitAddTorus.mFourierBasis (d := Fin 3)).repr.symm.toLinearIsometry.comp rawExtend

theorem type112FreqFun_single (S : Manhattan.Type112Index) (a : ℂ) :
    type112FreqFun (lp.single 2 S a) =
      a • mFourierLp 2 (Manhattan.type112RawIndex S) := by
  change (UnitAddTorus.mFourierBasis (d := Fin 3)).repr.symm
      (rawExtend (lp.single 2 S a)) = _
  rw [rawExtend, l2Extend_single, ← lp_single_smul, map_smul,
    HilbertBasis.repr_symm_single]
  simp

theorem mFourierCoeff_type112FreqFun (c : ℓ²(Manhattan.Type112Index, ℂ))
    (n : Manhattan.RawType112Index) :
    UnitAddTorus.mFourierCoeff (type112FreqFun c) n = rawExtend c n := by
  rw [← UnitAddTorus.mFourierBasis_repr]
  change (UnitAddTorus.mFourierBasis (d := Fin 3)).repr
      ((UnitAddTorus.mFourierBasis (d := Fin 3)).repr.symm (rawExtend c)) n = _
  rw [LinearIsometryEquiv.apply_symm_apply]

/-- Equation (20) for the type-`(1,1,2)` sector: the line-index Fourier
transform of a type-`(1,1,2)` coefficient lives entirely in the axis sector
`(horizontal, horizontal, vertical)`, where it is the `L²` function
`type112FreqFun`. -/
theorem lineIndexFourier_type112Extend (c : ℓ²(Manhattan.Type112Index, ℂ)) :
    lineIndexFourier 3 (type112Extend c) =
      lp.single 2 type112Pattern (type112FreqFun c) := by
  refine l2_ext' ((lineIndexFourier 3).toContinuousLinearMap.comp
      type112Extend.toContinuousLinearMap)
    (((freqSingle type112Pattern).comp type112FreqFun).toContinuousLinearMap) ?_ c
  intro S
  change lineIndexFourier 3 (type112Extend (lp.single 2 S (1 : ℂ))) =
    lp.single 2 type112Pattern (type112FreqFun (lp.single 2 S (1 : ℂ)))
  rw [type112Extend, l2Extend_single, lineIndexFourier_single, type112FreqFun_single,
    one_smul, one_smul, orderedFreqFamily, tuplePattern_degreeEnum_type112,
    tupleCoord_degreeEnum_type112]

end

end Manhattan.Glue

namespace Manhattan.Glue

noncomputable section

open MeasureTheory UnitAddTorus

/-! ### The transported quadratic forms -/

theorem integral_weight_zero (w : (Fin 3 → Axis) → UnitAddTorus (Fin 3) → ℝ)
    (σ : Fin 3 → Axis) :
    ∫ t, w σ t * ‖((0 : Lp ℂ 2 (LineTorusMeasure 3)) :
        UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2 ∂(LineTorusMeasure 3) = 0 := by
  rw [show (∫ t, w σ t * ‖((0 : Lp ℂ 2 (LineTorusMeasure 3)) :
      UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2 ∂(LineTorusMeasure 3)) =
      ∫ _t, (0 : ℝ) ∂(LineTorusMeasure 3) from ?_, integral_zero]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_zero ℂ 2 (LineTorusMeasure 3)] with t ht
  rw [ht]
  simp

/-- A quadratic form supported in the single axis sector `(h,h,v)`. -/
theorem tsum_single_integral
    (w : (Fin 3 → Axis) → UnitAddTorus (Fin 3) → ℝ)
    (F : Lp ℂ 2 (LineTorusMeasure 3)) :
    (∑' σ : Fin 3 → Axis, ∫ t, w σ t *
        ‖((lp.single (E := lineFreqFamily) 2 type112Pattern F : LineFreqL2 3) σ :
          UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2 ∂(LineTorusMeasure 3)) =
      ∫ t, w type112Pattern t *
        ‖(F : UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2 ∂(LineTorusMeasure 3) := by
  refine tsum_eq_single type112Pattern ?_ |>.trans ?_
  · intro σ hσ
    rw [lp.single_apply_ne (E := lineFreqFamily) 2 type112Pattern F hσ]
    exact integral_weight_zero w σ
  · rw [lp.single_apply_self (E := lineFreqFamily) 2 type112Pattern F]

/-- **The transport (T), `H` form.**  The degree-three `H` quadratic form of a
type-`(1,1,2)` coefficient is the explicit weighted integral of the squared
modulus of its line-frequency function. -/
theorem re_inner_coeffH_type112Extend (lam : ℝ) (p : Fin 2 → ℝ)
    (c : ℓ²(Manhattan.Type112Index, ℂ)) :
    RCLike.re (inner ℂ (coeffH 3 lam p (type112Extend c)) (type112Extend c)) =
      ∫ t, symbolWeight 3 lam p type112Pattern t *
        ‖(type112FreqFun c : UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2
        ∂(LineTorusMeasure 3) := by
  rw [re_inner_coeffH_eq_integral 3 lam p (type112Extend c),
    lineIndexFourier_type112Extend]
  exact tsum_single_integral (fun σ t => symbolWeight 3 lam p σ t) (type112FreqFun c)

/-- **The transport (T), `H⁻¹` form.**
-/
theorem re_inner_coeffH_inv_type112Extend {lam : ℝ} (hlam : 0 < lam)
    (p : Fin 2 → ℝ) (c d : ℓ²(Manhattan.Type112Index, ℂ))
    (hd : coeffH 3 lam p (type112Extend d) = type112Extend c) :
    RCLike.re (inner ℂ (type112Extend d) (type112Extend c)) =
      ∫ t, (symbolWeight 3 lam p type112Pattern t)⁻¹ *
        ‖(type112FreqFun c : UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2
        ∂(LineTorusMeasure 3) := by
  rw [re_inner_coeffH_inv_eq_integral 3 hlam p (type112Extend c) (type112Extend d) hd,
    lineIndexFourier_type112Extend]
  exact tsum_single_integral (fun σ t => (symbolWeight 3 lam p σ t)⁻¹)
    (type112FreqFun c)

/-- The degree-three `H` quadratic form on the Walsh fiber. -/
def hThreeForm (lam : ℝ) (p : Fin 2 → ℝ) : WalshL2 → ℝ := fun F =>
  RCLike.re (inner ℂ
    ((Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).H lam F) F)

/-- **The transport (T) in Walsh space.** -/
theorem hThreeForm_type112WalshSynthesis (lam : ℝ) (p : Fin 2 → ℝ)
    (c : ℓ²(Manhattan.Type112Index, ℂ)) :
    hThreeForm lam p (Manhattan.type112WalshSynthesis c) =
      ∫ t, symbolWeight 3 lam p type112Pattern t *
        ‖(type112FreqFun c : UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2
        ∂(LineTorusMeasure 3) := by
  rw [← re_inner_coeffH_type112Extend lam p c]
  unfold hThreeForm
  rw [type112WalshSynthesis_eq_homogeneous c,
    fiberH_homogeneousWalshSynthesis 3 lam p (type112Extend c),
    (homogeneousWalshSynthesis 3).inner_map_map]

end

end Manhattan.Glue

namespace Manhattan.Glue

noncomputable section

open MeasureTheory UnitAddTorus Set

/-! ### The manuscript's frequency variables -/

section Angles

attribute [local instance] Real.fact_zero_lt_one

theorem unitTorusAngle_eq_toIocMod (x : UnitAddCircle) :
    Manhattan.unitTorusAngle x =
      2 * Real.pi * toIocMod (Fact.out : (0:ℝ) < 1) (-(1/2 : ℝ)) (torusLift x) := by
  unfold Manhattan.unitTorusAngle
  congr 1
  change ((AddCircle.equivIoc (1 : ℝ) (-(1 / 2 : ℝ))) x : ℝ) = _
  conv_lhs => rw [← torusLift_coe x]
  rw [AddCircle.equivIoc, QuotientAddGroup.equivIocMod_coe]

/-- The physical frequency `2π` times the abstract representative differs from
the manuscript's `(-π,π]` angle by a multiple of `2π`. -/
theorem two_pi_torusLift (x : UnitAddCircle) :
    ∃ k : ℤ, 2 * Real.pi * torusLift x =
      Manhattan.unitTorusAngle x + k * (2 * Real.pi) := by
  refine ⟨toIocDiv (Fact.out : (0:ℝ) < 1) (-(1/2 : ℝ)) (torusLift x), ?_⟩
  rw [unitTorusAngle_eq_toIocMod]
  have h : toIocMod (Fact.out : (0:ℝ) < 1) (-(1/2 : ℝ)) (torusLift x) =
      torusLift x - toIocDiv (Fact.out : (0:ℝ) < 1) (-(1/2 : ℝ)) (torusLift x) • (1:ℝ) :=
    rfl
  rw [h]
  simp only [zsmul_eq_mul, mul_one]
  ring

end Angles

theorem dispersion_add_int_two_pi (y : ℝ) (k : ℤ) :
    Estimates.dispersion (y + k * (2 * Real.pi)) = Estimates.dispersion y := by
  unfold Estimates.dispersion
  rw [Real.cos_add_int_mul_two_pi]

theorem totalFrequency_type112_zero (p : Fin 2 → ℝ) (t : UnitAddTorus (Fin 3)) :
    totalFrequency 3 p type112Pattern t 0 = p 0 + 2 * Real.pi * torusLift (t 2) := by
  unfold totalFrequency lineFrequency
  rw [Fin.sum_univ_three]
  simp [lineShiftVector_axisVector, type112Pattern]

theorem totalFrequency_type112_one (p : Fin 2 → ℝ) (t : UnitAddTorus (Fin 3)) :
    totalFrequency 3 p type112Pattern t 1 =
      p 1 + 2 * Real.pi * (torusLift (t 0) + torusLift (t 1)) := by
  unfold totalFrequency lineFrequency
  rw [Fin.sum_univ_three]
  simp [lineShiftVector_axisVector, type112Pattern]

/-- The multiplier of (Hsym) for the type-`(1,1,2)` pattern at the shifted
momentum `(0, -p₂)` is exactly the manuscript's `H`-weight at the total
frequency `P = (β, r+r'-p₂)` of `Glue/CubicEnergy.lean`. -/
theorem symbolWeight_type112Pattern (lam p₂ : ℝ) (t : UnitAddTorus (Fin 3)) :
    symbolWeight 3 lam ![0, -p₂] type112Pattern t =
      lam + Estimates.theta (rawCorrectionTotalFrequency p₂ t) := by
  obtain ⟨k0, hk0⟩ := two_pi_torusLift (t 0)
  obtain ⟨k1, hk1⟩ := two_pi_torusLift (t 1)
  obtain ⟨k2, hk2⟩ := two_pi_torusLift (t 2)
  rw [symbolWeight_def]
  congr 1
  unfold Estimates.theta
  have h0 : Estimates.dispersion (totalFrequency 3 ![0, -p₂] type112Pattern t 0) =
      Estimates.dispersion (rawCorrectionTotalFrequency p₂ t 0) := by
    rw [totalFrequency_type112_zero]
    have : (0 : ℝ) + 2 * Real.pi * torusLift (t 2) =
        rawCorrectionTotalFrequency p₂ t 0 + k2 * (2 * Real.pi) := by
      rw [hk2]
      simp [rawCorrectionTotalFrequency, Estimates.mixedTotalFrequency]
    show Estimates.dispersion (![(0:ℝ), -p₂] 0 + 2 * Real.pi * torusLift (t 2)) = _
    rw [show ![(0:ℝ), -p₂] 0 = 0 from rfl, this, dispersion_add_int_two_pi]
  have h1 : Estimates.dispersion (totalFrequency 3 ![0, -p₂] type112Pattern t 1) =
      Estimates.dispersion (rawCorrectionTotalFrequency p₂ t 1) := by
    rw [totalFrequency_type112_one]
    have : (-p₂ : ℝ) + 2 * Real.pi * (torusLift (t 0) + torusLift (t 1)) =
        rawCorrectionTotalFrequency p₂ t 1 + ((k0 + k1 : ℤ) : ℝ) * (2 * Real.pi) := by
      have hexp : 2 * Real.pi * (torusLift (t 0) + torusLift (t 1)) =
          2 * Real.pi * torusLift (t 0) + 2 * Real.pi * torusLift (t 1) := by ring
      rw [hexp, hk0, hk1]
      simp only [rawCorrectionTotalFrequency, Estimates.mixedTotalFrequency,
        Matrix.cons_val_one, Matrix.cons_val_fin_one]
      push_cast
      ring
    show Estimates.dispersion (![(0:ℝ), -p₂] 1 +
      2 * Real.pi * (torusLift (t 0) + torusLift (t 1))) = _
    rw [show ![(0:ℝ), -p₂] 1 = -p₂ from rfl, this, dispersion_add_int_two_pi]
  rw [h0, h1]

theorem symbolWeight_eq_hWeight_type112 (q : Estimates.Parameters) (p₂ : ℝ)
    (t : UnitAddTorus (Fin 3)) :
    symbolWeight 3 q.lambda ![0, -p₂] type112Pattern t =
      Estimates.hWeight q (rawCorrectionTotalFrequency p₂ t) :=
  symbolWeight_type112Pattern q.lambda p₂ t

end

end Manhattan.Glue

namespace Manhattan.Glue

noncomputable section

open MeasureTheory UnitAddTorus Set

/-! ### The corrected coefficient of `Walsh/Correction.lean` -/

/-- **The transport for the actual corrected coefficient `k_p`.**  The
degree-three `H` quadratic form of `correctionWalsh` at the shifted momentum
`(0,-p₂)` is the manuscript's weighted integral
`∫ (λ + θ(P)) |k̂|²` with `P = (β, r+r'-p₂)`. -/
theorem hThreeForm_correctionWalsh {q : Estimates.Parameters}
    (hlambda : 0 < q.lambda) (a p₂ : ℝ) :
    hThreeForm q.lambda ![0, -p₂]
        (Manhattan.correctionWalsh (kappa := 40) (by norm_num) hlambda a p₂) =
      ∫ t, Estimates.hWeight q (rawCorrectionTotalFrequency p₂ t) *
        ‖(type112FreqFun (Manhattan.correctionType112Coefficients
            (kappa := 40) (by norm_num) hlambda a p₂) :
          UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2 ∂(LineTorusMeasure 3) := by
  have hsyn : Manhattan.correctionWalsh (kappa := 40) (by norm_num) hlambda a p₂ =
      Manhattan.type112WalshSynthesis (Manhattan.correctionType112Coefficients
        (kappa := 40) (by norm_num) hlambda a p₂) := rfl
  rw [hsyn, hThreeForm_type112WalshSynthesis]
  simp only [symbolWeight_eq_hWeight_type112]

end

end Manhattan.Glue

namespace Manhattan.Glue

noncomputable section

open MeasureTheory UnitAddTorus Set

/-! ### Pointwise values of the extension by zero -/

theorem l2_eval {κ : Type*} [DecidableEq κ] (c : ℓ²(κ, ℂ)) (k : κ) :
    c k = inner ℂ (lp.single 2 k (1 : ℂ)) c := by
  rw [lp.inner_single_left]
  simp

theorem l2Extend_apply_image {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (f : ι → κ) (hf : Function.Injective f) (c : ℓ²(ι, ℂ)) (i : ι) :
    l2Extend f hf c (f i) = c i := by
  rw [l2_eval (l2Extend f hf c) (f i), l2_eval c i]
  refine l2_ext'
    ((innerSL ℂ (lp.single 2 (f i) (1 : ℂ))).comp
      (l2Extend f hf).toContinuousLinearMap)
    (innerSL ℂ (lp.single 2 i (1 : ℂ))) ?_ c
  intro j
  change inner ℂ (lp.single 2 (f i) (1 : ℂ))
      (l2Extend f hf (lp.single 2 j (1 : ℂ) : ℓ²(ι, ℂ))) =
    inner ℂ (lp.single 2 i (1 : ℂ)) (lp.single 2 j (1 : ℂ) : ℓ²(ι, ℂ))
  rw [l2Extend_single, lp.inner_single_left, lp.inner_single_left]
  simp only [lp.single_apply, Pi.single_apply]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg h, if_neg (show ¬ (f i = f j) from fun hc => h (hf hc))]

theorem l2Extend_apply_of_notMem {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (f : ι → κ) (hf : Function.Injective f) (c : ℓ²(ι, ℂ)) (k : κ)
    (hk : ∀ i, f i ≠ k) : l2Extend f hf c k = 0 := by
  rw [l2_eval (l2Extend f hf c) k]
  refine l2_ext'
    ((innerSL ℂ (lp.single 2 k (1 : ℂ))).comp (l2Extend f hf).toContinuousLinearMap)
    0 ?_ c
  intro j
  change inner ℂ (lp.single 2 k (1 : ℂ))
    (l2Extend f hf (lp.single 2 j (1 : ℂ) : ℓ²(ι, ℂ))) = 0
  rw [l2Extend_single, lp.inner_single_left]
  simp only [lp.single_apply, Pi.single_apply]
  rw [if_neg (show ¬ (k = f j) from fun hc => hk j hc.symm)]
  simp

theorem exists_type112RawIndex {n : Manhattan.RawType112Index} (h : n 0 < n 1) :
    ∃ S : Manhattan.Type112Index, Manhattan.type112RawIndex S = n :=
  ⟨Manhattan.orderedType112Equiv ⟨n, h⟩, by
    change (Manhattan.orderedType112Equiv.symm
      (Manhattan.orderedType112Equiv ⟨n, h⟩)).1 = n
    rw [Equiv.symm_apply_apply]⟩

theorem range_type112RawIndex :
    Set.range Manhattan.type112RawIndex =
      {n : Manhattan.RawType112Index | n 0 < n 1} := by
  ext n
  constructor
  · rintro ⟨S, rfl⟩
    exact type112RawIndex_lt S
  · intro h
    exact exists_type112RawIndex h

/-- The Fourier-coefficient description of the coincident-row projection:
`Π₃` restricts the raw coefficient sequence to the strictly ordered row
pairs.
-/
theorem rawExtend_type112DiagonalProjection_apply
    (d : ℓ²(Manhattan.RawType112Index, ℂ)) (n : Manhattan.RawType112Index) :
    rawExtend (Manhattan.type112DiagonalProjection d) n =
      if n 0 < n 1 then d n else 0 := by
  by_cases h : n 0 < n 1
  · obtain ⟨S, rfl⟩ := exists_type112RawIndex h
    rw [if_pos h, rawExtend,
      l2Extend_apply_image _ Manhattan.type112RawIndex_injective _ S]
    rfl
  · rw [if_neg h, rawExtend]
    refine l2Extend_apply_of_notMem _ Manhattan.type112RawIndex_injective _ n ?_
    intro S hS
    exact h (hS ▸ type112RawIndex_lt S)

end

end Manhattan.Glue

namespace Manhattan.Glue

noncomputable section

open MeasureTheory UnitAddTorus

/-! ### The `(shift)` phase as a translation of the frequency torus

`Manhattan.type112ShiftTwist` multiplies the type-`(1,1,2)` coefficients by the
character `e^{i(m+m')p₂+inp₁}` of `manuscript.tex:791-800`.  On the frequency
side that character is a translation of the three-dimensional line-frequency
torus by `Manhattan.shiftTorusPoint`, so the degree-three `H` quadratic form of
a twisted coefficient at the momentum `P` is the form of the untwisted one at
the momentum `P` moved by `(p₁, 2p₂)`.  At the true frozen momentum `p`, with
`p₁ = p 0` and `p₂ = p 1`, the moved momentum is exactly `(0,-p₂)`:
the factor-two comparison of `hThreeForm_type112_le` becomes an identity.
-/

/-- The multivariate character is multiplicative in its argument. -/
theorem mFourier_add_arg {n : ℕ} (m : Fin n → ℤ) (x y : UnitAddTorus (Fin n)) :
    mFourier m (x + y) = mFourier m x * mFourier m y := by
  show (∏ i : Fin n, fourier (m i) ((x + y) i)) =
    (∏ i : Fin n, fourier (m i) (x i)) * (∏ i : Fin n, fourier (m i) (y i))
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  show fourier (m i) (x i + y i) = _
  rw [fourier_apply, fourier_apply, fourier_apply, smul_add,
    AddCircle.toCircle_add, Circle.coe_mul]

/-- Translation of the three-dimensional line-frequency torus, as a linear
isometry of `L²`. -/
def torusShift (θ : UnitAddTorus (Fin 3)) :
    Lp ℂ 2 (LineTorusMeasure 3) →ₗᵢ[ℂ] Lp ℂ 2 (LineTorusMeasure 3) :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun t => t + θ) (measurePreserving_add_right _ _)

theorem coeFn_torusShift (θ : UnitAddTorus (Fin 3))
    (F : Lp ℂ 2 (LineTorusMeasure 3)) :
    (torusShift θ F : UnitAddTorus (Fin 3) → ℂ) =ᵐ[LineTorusMeasure 3]
      fun t => F (t + θ) :=
  Lp.coeFn_compMeasurePreserving F (measurePreserving_add_right _ _)

theorem torusShift_mFourierLp (θ : UnitAddTorus (Fin 3))
    (n : Manhattan.RawType112Index) :
    torusShift θ (mFourierLp 2 n) = mFourier n θ • mFourierLp 2 n := by
  have hmp : MeasurePreserving (fun t : UnitAddTorus (Fin 3) => t + θ)
      (LineTorusMeasure 3) (LineTorusMeasure 3) := measurePreserving_add_right _ _
  refine Lp.ext ?_
  have h1 := coeFn_torusShift θ (mFourierLp 2 n)
  have h2 : (fun t : UnitAddTorus (Fin 3) => (mFourierLp 2 n : _ → ℂ) (t + θ))
      =ᵐ[LineTorusMeasure 3] fun t => mFourier n (t + θ) :=
    hmp.quasiMeasurePreserving.ae_eq_comp (coeFn_mFourierLp 2 n)
  have h3 := Lp.coeFn_smul (mFourier n θ) (mFourierLp 2 n)
  have h4 := coeFn_mFourierLp (d := Fin 3) 2 n
  filter_upwards [h1, h2, h3, h4] with t ht1 ht2 ht3 ht4
  rw [ht1, ht2, ht3]
  show mFourier n (t + θ) = mFourier n θ • (mFourierLp 2 n : _ → ℂ) t
  rw [ht4, mFourier_add_arg, smul_eq_mul, mul_comm]

/-- The (shift) phase acts on the line-frequency function by translation. -/
theorem type112FreqFun_type112ShiftTwist (p₁ p₂ : ℝ)
    (c : ℓ²(Manhattan.Type112Index, ℂ)) :
    type112FreqFun (Manhattan.type112ShiftTwist p₁ p₂ c) =
      torusShift (Manhattan.shiftTorusPoint p₁ p₂) (type112FreqFun c) := by
  refine l2_ext' (type112FreqFun.toContinuousLinearMap.comp
      (Manhattan.type112ShiftTwist p₁ p₂).toContinuousLinearMap)
    ((torusShift (Manhattan.shiftTorusPoint p₁ p₂)).toContinuousLinearMap.comp
      type112FreqFun.toContinuousLinearMap) ?_ c
  intro S
  change type112FreqFun (Manhattan.type112ShiftTwist p₁ p₂
      (lp.single 2 S (1 : ℂ))) =
    torusShift (Manhattan.shiftTorusPoint p₁ p₂)
      (type112FreqFun (lp.single 2 S (1 : ℂ)))
  rw [Manhattan.type112ShiftTwist_single, type112FreqFun_single,
    type112FreqFun_single, one_smul, mul_one, torusShift_mFourierLp]
  rfl

/-- A real lift of a translated frequency differs from the sum of the lifts by
a multiple of `2π`. -/
theorem torusLift_add_shift (x : UnitAddCircle) (v : ℝ) :
    ∃ k : ℤ, 2 * Real.pi *
        torusLift (x + ((v / (2 * Real.pi) : ℝ) : UnitAddCircle)) =
      2 * Real.pi * torusLift x + v + k * (2 * Real.pi) := by
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  set y : ℝ := torusLift (x + ((v / (2 * Real.pi) : ℝ) : UnitAddCircle)) with hy
  have hcoe : ((y : ℝ) : UnitAddCircle) =
      ((torusLift x + v / (2 * Real.pi) : ℝ) : UnitAddCircle) := by
    rw [hy, torusLift_coe]
    rw [show ((torusLift x + v / (2 * Real.pi) : ℝ) : UnitAddCircle) =
        ((torusLift x : ℝ) : UnitAddCircle) +
          ((v / (2 * Real.pi) : ℝ) : UnitAddCircle) from rfl, torusLift_coe]
  have hzero : ((y - (torusLift x + v / (2 * Real.pi)) : ℝ) : UnitAddCircle) = 0 := by
    rw [show ((y - (torusLift x + v / (2 * Real.pi)) : ℝ) : UnitAddCircle) =
        ((y : ℝ) : UnitAddCircle) -
          ((torusLift x + v / (2 * Real.pi) : ℝ) : UnitAddCircle) from rfl, hcoe,
      sub_self]
  obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff _).1 hzero
  refine ⟨k, ?_⟩
  have hk' : (k : ℝ) = y - (torusLift x + v / (2 * Real.pi)) := by
    simpa using hk
  have hyval : y = torusLift x + v / (2 * Real.pi) + (k : ℝ) := by linarith
  rw [hyval]
  field_simp

/-- The `(Hsym)` symbol of the type-`(1,1,2)` pattern at a translated frequency
is the symbol at a translated momentum. -/
theorem symbolWeight_type112_add_shiftTorusPoint (lam : ℝ) (P : Fin 2 → ℝ)
    (p₁ p₂ : ℝ) (t : UnitAddTorus (Fin 3)) :
    symbolWeight 3 lam P type112Pattern (t + Manhattan.shiftTorusPoint p₁ p₂) =
      symbolWeight 3 lam ![P 0 + p₁, P 1 + (p₂ + p₂)] type112Pattern t := by
  obtain ⟨k0, hk0⟩ := torusLift_add_shift (t 0) p₂
  obtain ⟨k1, hk1⟩ := torusLift_add_shift (t 1) p₂
  obtain ⟨k2, hk2⟩ := torusLift_add_shift (t 2) p₁
  have e0 : (t + Manhattan.shiftTorusPoint p₁ p₂) 0 =
      t 0 + ((p₂ / (2 * Real.pi) : ℝ) : UnitAddCircle) := rfl
  have e1 : (t + Manhattan.shiftTorusPoint p₁ p₂) 1 =
      t 1 + ((p₂ / (2 * Real.pi) : ℝ) : UnitAddCircle) := rfl
  have e2 : (t + Manhattan.shiftTorusPoint p₁ p₂) 2 =
      t 2 + ((p₁ / (2 * Real.pi) : ℝ) : UnitAddCircle) := rfl
  rw [← e0] at hk0
  rw [← e1] at hk1
  rw [← e2] at hk2
  rw [symbolWeight_def, symbolWeight_def]
  congr 1
  unfold Manhattan.Estimates.theta
  have h0 : Manhattan.Estimates.dispersion
        (totalFrequency 3 P type112Pattern
          (t + Manhattan.shiftTorusPoint p₁ p₂) 0) =
      Manhattan.Estimates.dispersion
        (totalFrequency 3 ![P 0 + p₁, P 1 + (p₂ + p₂)] type112Pattern t 0) := by
    rw [totalFrequency_type112_zero, totalFrequency_type112_zero,
      show ![P 0 + p₁, P 1 + (p₂ + p₂)] 0 = P 0 + p₁ from rfl]
    have key : P 0 + 2 * Real.pi *
          torusLift ((t + Manhattan.shiftTorusPoint p₁ p₂) 2) =
        (P 0 + p₁ + 2 * Real.pi * torusLift (t 2)) + (k2 : ℝ) * (2 * Real.pi) := by
      rw [hk2]; ring
    rw [key, dispersion_add_int_two_pi]
  have h1 : Manhattan.Estimates.dispersion
        (totalFrequency 3 P type112Pattern
          (t + Manhattan.shiftTorusPoint p₁ p₂) 1) =
      Manhattan.Estimates.dispersion
        (totalFrequency 3 ![P 0 + p₁, P 1 + (p₂ + p₂)] type112Pattern t 1) := by
    rw [totalFrequency_type112_one, totalFrequency_type112_one,
      show ![P 0 + p₁, P 1 + (p₂ + p₂)] 1 = P 1 + (p₂ + p₂) from rfl]
    have key : P 1 + 2 * Real.pi *
          (torusLift ((t + Manhattan.shiftTorusPoint p₁ p₂) 0) +
            torusLift ((t + Manhattan.shiftTorusPoint p₁ p₂) 1)) =
        (P 1 + (p₂ + p₂) + 2 * Real.pi * (torusLift (t 0) + torusLift (t 1))) +
          ((k0 + k1 : ℤ) : ℝ) * (2 * Real.pi) := by
      have e : 2 * Real.pi *
            (torusLift ((t + Manhattan.shiftTorusPoint p₁ p₂) 0) +
              torusLift ((t + Manhattan.shiftTorusPoint p₁ p₂) 1)) =
          2 * Real.pi * torusLift ((t + Manhattan.shiftTorusPoint p₁ p₂) 0) +
            2 * Real.pi * torusLift ((t + Manhattan.shiftTorusPoint p₁ p₂) 1) := by
        ring
      rw [e, hk0, hk1]
      push_cast
      ring
    rw [key, dispersion_add_int_two_pi]
  rw [h0, h1]

/-- **The (shift) phase moves the momentum of the degree-three `H` form.** -/
theorem hThreeForm_type112ShiftTwist (lam : ℝ) (P : Fin 2 → ℝ) (p₁ p₂ : ℝ)
    (c : ℓ²(Manhattan.Type112Index, ℂ)) :
    hThreeForm lam P
        (Manhattan.type112WalshSynthesis (Manhattan.type112ShiftTwist p₁ p₂ c)) =
      hThreeForm lam ![P 0 - p₁, P 1 - (p₂ + p₂)]
        (Manhattan.type112WalshSynthesis c) := by
  have hmom : (![![P 0 - p₁, P 1 - (p₂ + p₂)] 0 + p₁,
      ![P 0 - p₁, P 1 - (p₂ + p₂)] 1 + (p₂ + p₂)] : Fin 2 → ℝ) = P := by
    funext i
    fin_cases i <;> simp
  have hsymb : ∀ t : UnitAddTorus (Fin 3),
      symbolWeight 3 lam ![P 0 - p₁, P 1 - (p₂ + p₂)] type112Pattern
          (t + Manhattan.shiftTorusPoint p₁ p₂) =
        symbolWeight 3 lam P type112Pattern t := fun t => by
    rw [symbolWeight_type112_add_shiftTorusPoint, hmom]
  have hshift := integral_add_right_eq_self (μ := LineTorusMeasure 3)
    (fun s : UnitAddTorus (Fin 3) =>
      symbolWeight 3 lam ![P 0 - p₁, P 1 - (p₂ + p₂)] type112Pattern s *
        ‖(type112FreqFun c : UnitAddTorus (Fin 3) → ℂ) s‖ ^ 2)
    (Manhattan.shiftTorusPoint p₁ p₂)
  rw [hThreeForm_type112WalshSynthesis, hThreeForm_type112WalshSynthesis,
    type112FreqFun_type112ShiftTwist, ← hshift]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_torusShift (Manhattan.shiftTorusPoint p₁ p₂)
    (type112FreqFun c)] with t ht
  rw [ht, hsymb t]

/-- **The exact form of the momentum bridge at the true frozen momentum.**  The
degree-three `H` quadratic form of the competitor's phase-twisted coefficient at
the momentum `p` is exactly form at the frozen momentum `(0,-p₂)`. -/
theorem hThreeForm_type112ShiftTwist_frozen (lam : ℝ) (p : Fin 2 → ℝ)
    (c : ℓ²(Manhattan.Type112Index, ℂ)) :
    hThreeForm lam p
        (Manhattan.type112WalshSynthesis
          (Manhattan.type112ShiftTwist (p 0) (p 1) c)) =
      hThreeForm lam ![0, -(p 1)] (Manhattan.type112WalshSynthesis c) := by
  rw [hThreeForm_type112ShiftTwist]
  congr 1
  funext i
  fin_cases i <;> simp

end

end Manhattan.Glue
