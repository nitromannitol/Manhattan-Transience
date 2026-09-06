import Manhattan.Model.LowDegree

/-!
# Complete degree-two Walsh sectors and the lowering part of the skew fiber

The paper writes degree-two coefficients in ordered tuple coordinates.  Here
the two-row and mixed sectors are indexed directly by two-element Finsets.
Their synthesis and analysis maps therefore have no factorial rescaling.

The signed lowering operator `D₂*` is defined as the degree-two coordinate
part of `-A`; this agrees with the convention `A = D - D*` already proved on
every Walsh basis vector in `Manhattan.Model.LowDegree`.

Paper: `manuscript.tex:719-740`, `manuscript.tex:822-840`, and
`manuscript.tex:1238-1255`.
-/

open ComplexConjugate InnerProductSpace

namespace Manhattan

noncomputable section

/-- Classical decidability, local to this file: the statements here are analytic, not computational. -/
local instance lowDegreeSectorsPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- A two-row Finset index. -/
def IsType11Index (S : Finset LineIndex) : Prop :=
  S.card = 2 ∧ ∀ l ∈ S, l.1 = Axis.horizontal

/-- A mixed Finset index, containing one row and one column. -/
def IsType12Index (S : Finset LineIndex) : Prop :=
  S.card = 2 ∧ (S.filter fun l => l.1 = Axis.horizontal).card = 1

/-- The genuine Finset carrier for the two-row degree-two sector. -/
abbrev Type11Index := {S : Finset LineIndex // IsType11Index S}

/-- The genuine Finset carrier for the mixed degree-two sector. -/
abbrev Type12Index := {S : Finset LineIndex // IsType12Index S}

/-- Restriction of the full Walsh analysis map to an arbitrary subtype of
Finset indices. -/
noncomputable def walshSectorAnalysis (P : Finset LineIndex → Prop)
    (x : WalshL2) : ℓ²({S : Finset LineIndex // P S}, ℂ) :=
  ⟨fun S => walshBasis.repr x S.1, by
    apply memℓp_gen
    simpa using ((lp.memℓp (walshBasis.repr x)).summable (by norm_num)).comp_injective
      Subtype.val_injective⟩

@[simp] theorem walshSectorAnalysis_apply (P : Finset LineIndex → Prop)
    (x : WalshL2) (S : {S : Finset LineIndex // P S}) :
    walshSectorAnalysis P x S = inner ℂ (walshL2 S.1) x := by
  rw [walshSectorAnalysis, walshBasis.repr_apply_apply, walshBasis_apply]

/-- Analysis on the two-row sector. -/
noncomputable def type11WalshAnalysis (x : WalshL2) : ℓ²(Type11Index, ℂ) :=
  walshSectorAnalysis IsType11Index x

/-- Analysis on the mixed sector. -/
noncomputable def type12WalshAnalysis (x : WalshL2) : ℓ²(Type12Index, ℂ) :=
  walshSectorAnalysis IsType12Index x

/-- The two-row Walsh family. -/
def type11WalshFamily (S : Type11Index) : WalshL2 := walshL2 S.1

/-- The mixed Walsh family. -/
def type12WalshFamily (S : Type12Index) : WalshL2 := walshL2 S.1

theorem orthonormal_type11WalshFamily : Orthonormal ℂ type11WalshFamily :=
  orthonormal_walshL2.comp Subtype.val Subtype.val_injective

theorem orthonormal_type12WalshFamily : Orthonormal ℂ type12WalshFamily :=
  orthonormal_walshL2.comp Subtype.val Subtype.val_injective

/-- Complete two-row Finset synthesis. -/
noncomputable def type11WalshSynthesis : ℓ²(Type11Index, ℂ) →ₗᵢ[ℂ] WalshL2 :=
  orthonormal_type11WalshFamily.orthogonalFamily.linearIsometry

/-- Complete mixed Finset synthesis. -/
noncomputable def type12WalshSynthesis : ℓ²(Type12Index, ℂ) →ₗᵢ[ℂ] WalshL2 :=
  orthonormal_type12WalshFamily.orthogonalFamily.linearIsometry

theorem norm_type11WalshSynthesis (c : ℓ²(Type11Index, ℂ)) :
    ‖type11WalshSynthesis c‖ = ‖c‖ :=
  type11WalshSynthesis.norm_map c

theorem norm_type12WalshSynthesis (c : ℓ²(Type12Index, ℂ)) :
    ‖type12WalshSynthesis c‖ = ‖c‖ :=
  type12WalshSynthesis.norm_map c

/-- A coefficient of the complete type-`112` synthesis, extended by zero to
all Walsh Finsets. -/
noncomputable def type112CoefficientAt (c : ℓ²(Type112Index, ℂ))
    (S : Finset LineIndex) : ℂ :=
  if hS : IsType112Index S then c ⟨S, hS⟩ else 0

/-- Coefficient extraction from the complete type-`112` synthesis. -/
theorem inner_walshL2_type112WalshSynthesis
    (c : ℓ²(Type112Index, ℂ)) (S : Finset LineIndex) :
    inner ℂ (walshL2 S) (type112WalshSynthesis c) =
      type112CoefficientAt c S := by
  classical
  by_cases hS : IsType112Index S
  · let T : Type112Index := ⟨S, hS⟩
    have hone : type112WalshSynthesis (lp.single 2 T (1 : ℂ)) = walshL2 S := by
      rw [type112WalshSynthesis_single, one_smul]
    rw [← hone, type112WalshSynthesis.inner_map_map, lp.inner_single_left]
    simp [type112CoefficientAt, hS, T]
  · rw [type112CoefficientAt, dif_neg hS]
    have hs : HasSum (fun T : Type112Index => c T • walshL2 T.1)
        (type112WalshSynthesis c) := by
      simpa only [type112WalshSynthesis, type112WalshFamily,
        LinearIsometry.toSpanSingleton_apply] using
        orthonormal_type112WalshFamily.orthogonalFamily.hasSum_linearIsometry c
    have hm := hs.mapL (innerSL ℂ (walshL2 S))
    have hz : HasSum (fun _ : Type112Index => (0 : ℂ)) 0 := hasSum_zero
    apply hm.unique
    apply HasSum.congr_fun hz
    intro T
    simp only [innerSL_apply_apply, inner_smul_right, inner_walshL2]
    rw [if_neg]
    · simp
    · intro hST
      apply hS
      rw [hST]
      exact T.2

/-- Pairing a finite Walsh coefficient with the complete type-`112`
synthesis is the literal Finset coefficient sum. -/
theorem inner_walshSynthesis_type112WalshSynthesis
    (a : WalshCoefficient) (c : ℓ²(Type112Index, ℂ)) :
    inner ℂ (walshSynthesis a) (type112WalshSynthesis c) =
      a.sum fun S z => conj z * type112CoefficientAt c S := by
  classical
  rw [walshSynthesis, Finsupp.linearCombination_apply, Finsupp.sum_inner]
  apply Finsupp.sum_congr
  intro S _
  rw [inner_walshL2_type112WalshSynthesis]
  simp only [smul_eq_mul]

/-- The exact type-`11` component of `D₂*`, in the no-factorial Finset
isometry. -/
noncomputable def type112DStarTwoRow (p : Fin 2 → ℝ)
    (c : ℓ²(Type112Index, ℂ)) : ℓ²(Type11Index, ℂ) :=
  type11WalshAnalysis (-concreteFiberA p (type112WalshSynthesis c))

/-- The exact type-`12` component of `D₂*`, in the no-factorial Finset
isometry. -/
noncomputable def type112DStarMixed (p : Fin 2 → ℝ)
    (c : ℓ²(Type112Index, ℂ)) : ℓ²(Type12Index, ℂ) :=
  type12WalshAnalysis (-concreteFiberA p (type112WalshSynthesis c))

/-- The complete degree-two lowering vector, split into its orthogonal
two-row and mixed Finset sectors. -/
noncomputable def type112DStar (p : Fin 2 → ℝ)
    (c : ℓ²(Type112Index, ℂ)) : WalshL2 :=
  type11WalshSynthesis (type112DStarTwoRow p c) +
    type12WalshSynthesis (type112DStarMixed p c)

/-- Adjoint characterization of the two-row lowering coefficient.  There is
no `sqrt 2` or factorial: all three synthesis maps are literal isometries. -/
theorem type112DStarTwoRow_apply (p : Fin 2 → ℝ)
    (c : ℓ²(Type112Index, ℂ)) (T : Type11Index) :
    type112DStarTwoRow p c T =
      inner ℂ (concreteFiberA p (walshL2 T.1)) (type112WalshSynthesis c) := by
  rw [type112DStarTwoRow, type11WalshAnalysis,
    walshSectorAnalysis_apply, inner_neg_right]
  rw [← (concreteFiberA p).adjoint_inner_left,
    concreteFiberA_skewAdjoint, ContinuousLinearMap.neg_apply,
    inner_neg_left]
  simp

/-- Spatial Finset form of (D2a).  The finite sum is the actual raising
coefficient of `A` on the test index, paired with the complete type-`112`
coefficient. -/
theorem type112DStarTwoRow_apply_finset (p : Fin 2 → ℝ)
    (c : ℓ²(Type112Index, ℂ)) (T : Type11Index) :
    type112DStarTwoRow p c T =
      (fiberASpatialCoefficient p T.1).sum fun S z =>
        conj z * type112CoefficientAt c S := by
  rw [type112DStarTwoRow_apply, concreteFiberA_walshL2,
    inner_walshSynthesis_type112WalshSynthesis]

/-- Adjoint characterization of the mixed lowering coefficient.  In Finset
coordinates its normalization is one; the manuscript's tuple-space `sqrt 2`
is not imported. -/
theorem type112DStarMixed_apply (p : Fin 2 → ℝ)
    (c : ℓ²(Type112Index, ℂ)) (T : Type12Index) :
    type112DStarMixed p c T =
      inner ℂ (concreteFiberA p (walshL2 T.1)) (type112WalshSynthesis c) := by
  rw [type112DStarMixed, type12WalshAnalysis,
    walshSectorAnalysis_apply, inner_neg_right]
  rw [← (concreteFiberA p).adjoint_inner_left,
    concreteFiberA_skewAdjoint, ContinuousLinearMap.neg_apply,
    inner_neg_left]
  simp

/-- Spatial Finset form of (D2b).  Unlike the ordered-tuple display in the
manuscript, this exact isometric formula has no external `sqrt 2` factor. -/
theorem type112DStarMixed_apply_finset (p : Fin 2 → ℝ)
    (c : ℓ²(Type112Index, ℂ)) (T : Type12Index) :
    type112DStarMixed p c T =
      (fiberASpatialCoefficient p T.1).sum fun S z =>
        conj z * type112CoefficientAt c S := by
  rw [type112DStarMixed_apply, concreteFiberA_walshL2,
    inner_walshSynthesis_type112WalshSynthesis]

end

end Manhattan
