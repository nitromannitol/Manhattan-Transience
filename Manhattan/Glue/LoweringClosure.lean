import Manhattan.Glue.ConcreteLoweringFourier
import Manhattan.Glue.ProjectionDischargeIndex

/-!
# The `L²` closure of the concrete lowering formulas (D2a), (D2b)

`Manhattan.Glue.ConcreteLoweringFourier` proves the two lowering formulas for a
*finitely supported* ordered type-`112` kernel, i.e. for a Walsh polynomial.
This file removes that restriction.

Both sides of each formula are continuous linear functionals of the input
vector: the left-hand side is `x ↦ ⟪A_p (walshL2 S), x⟫` by
`Manhattan.Glue.loweringCoefficient`, and the right-hand side is a fixed finite
linear combination of the Walsh coefficient functionals `x ↦ ⟪walshL2 S, x⟫`.
The finite type-`112` Walsh polynomials are dense in the range of the complete
type-`112` synthesis `Manhattan.type112WalshSynthesis`, which is an isometry
of `ℓ²(Type112Index, ℂ)` onto that closed subspace.  Two continuous functionals
that agree on a spanning set therefore agree on the whole closed sector, so the
formulas hold for an arbitrary square-summable type-`112` coefficient.

The statements below are the `L²` forms of (D2a) and (D2b) in the Finset
(spatial) coordinates of.  They are stated with no symmetry and no
diagonal-freeness hypothesis: a Finset index carries distinctness by
construction, and the coefficient of a type-`112` vector at a non-type-`112`
index vanishes.

Paper: `manuscript.tex:793-840`.
-/

open ComplexConjugate InnerProductSpace

namespace Manhattan.Glue

noncomputable section

/-- Classical decidability, local to this file: the statements here are analytic, not computational. -/
local instance loweringClosurePropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-! ## The type-`112` sector -/

/-- A vector whose Walsh coefficients are carried by the type-`112` indices. -/
def IsType112Supported (x : WalshL2) : Prop :=
  ∀ S : Finset LineIndex, ¬ IsType112Index S → walshCoefficientAt x S = 0

theorem isType112Supported_walshL2 (T : Type112Index) :
    IsType112Supported (walshL2 T.1) := by
  intro S hS
  rw [walshCoefficientAt, inner_walshL2, if_neg]
  intro hST
  exact hS (hST ▸ T.2)

theorem isType112Supported_type112WalshSynthesis (c : ℓ²(Type112Index, ℂ)) :
    IsType112Supported (type112WalshSynthesis c) := by
  intro S hS
  rw [walshCoefficientAt, inner_walshL2_type112WalshSynthesis,
    type112CoefficientAt, dif_neg hS]

theorem isType112Supported_walshSynthesis (k : (ℤ × ℤ × ℤ) →₀ ℂ) :
    IsType112Supported (walshSynthesis (type112FinsetCoefficient k)) := by
  intro S hS
  rw [walshCoefficientAt_walshSynthesis]
  exact type112FinsetCoefficient_eq_zero_of_not_isType112 k hS

/-! ## Failure of the type-`112` pattern on a repeated row -/

theorem tripleToFinset_diag (a c : ℤ) :
    tripleToFinset (a, a, c) =
      ({(Axis.horizontal, a), (Axis.vertical, c)} : Finset LineIndex) := by
  ext l
  simp only [tripleToFinset, Finset.mem_insert, Finset.mem_singleton]
  tauto

theorem not_isType112_tripleToFinset_diag (a c : ℤ) :
    ¬ IsType112Index (tripleToFinset (a, a, c)) := by
  refine not_isType112_of_card_ne ?_
  rw [tripleToFinset_diag]
  simp

/-! ## (D2a) and (D2b) on the whole type-`112` sector -/

/-- **(D2a) on all of `L²`.**  For every vector carried by the type-`112`
indices the two-row Walsh coefficient of `D₂* x` is one signed lattice step in
*both* row indices, with the column index of the input pinned to the origin.
No finite support, no symmetry and no diagonal-freeness hypothesis is used. -/
theorem loweringCoefficient_rowPair_of_supported (p : Fin 2 → ℝ) {x : WalshL2}
    (hx : IsType112Supported x) (m m' : ℤ) :
    loweringCoefficient p x (rowPairFinset (m, m')) =
      ((2 : ℂ)⁻¹ * Complex.exp (-Complex.I * p 1)) *
          walshCoefficientAt x (tripleToFinset (m + 1, m' + 1, 0)) -
        ((2 : ℂ)⁻¹ * Complex.exp (Complex.I * p 1)) *
          walshCoefficientAt x (tripleToFinset (m - 1, m' - 1, 0)) := by
  have e0p : translateWalshIndex (Operator.axisVector 0) (rowPairFinset (m, m'))
      = rowPairFinset (m, m') := by
    rw [translateWalshIndex_rowPair]; simp
  have e0m : translateWalshIndex (-Operator.axisVector 0) (rowPairFinset (m, m'))
      = rowPairFinset (m, m') := by
    rw [translateWalshIndex_rowPair]; simp
  have e1p : translateWalshIndex (Operator.axisVector 1) (rowPairFinset (m, m'))
      = rowPairFinset (m + 1, m' + 1) := by
    rw [translateWalshIndex_rowPair]; simp
  have e1m : translateWalshIndex (-Operator.axisVector 1) (rowPairFinset (m, m'))
      = rowPairFinset (m - 1, m' - 1) := by
    rw [translateWalshIndex_rowPair]; simp [sub_eq_add_neg]
  rw [loweringCoefficient_eq, Fin.sum_univ_two, e0p, e0m, e1p, e1m,
    toggle_vertical_rowPair, toggle_vertical_rowPair,
    hx _ (not_isType112_toggle_horizontal_rowPair m m')]
  ring

/-- **(D2b) on all of `L²`.**  For every vector carried by the type-`112`
indices the mixed Walsh coefficient of `D₂* x` is one signed lattice step in the
column index, with the second row index of the input pinned to the origin. -/
theorem loweringCoefficient_mixedPair_of_supported (p : Fin 2 → ℝ) {x : WalshL2}
    (hx : IsType112Supported x) (m n : ℤ) :
    loweringCoefficient p x (mixedPairFinset (m, n)) =
      ((2 : ℂ)⁻¹ * Complex.exp (-Complex.I * p 0)) *
          walshCoefficientAt x (tripleToFinset (m, 0, n + 1)) -
        ((2 : ℂ)⁻¹ * Complex.exp (Complex.I * p 0)) *
          walshCoefficientAt x (tripleToFinset (m, 0, n - 1)) := by
  have e0p : translateWalshIndex (Operator.axisVector 0) (mixedPairFinset (m, n))
      = mixedPairFinset (m, n + 1) := by
    rw [translateWalshIndex_mixedPair]; simp
  have e0m : translateWalshIndex (-Operator.axisVector 0) (mixedPairFinset (m, n))
      = mixedPairFinset (m, n - 1) := by
    rw [translateWalshIndex_mixedPair]; simp [sub_eq_add_neg]
  have e1p : translateWalshIndex (Operator.axisVector 1) (mixedPairFinset (m, n))
      = mixedPairFinset (m + 1, n) := by
    rw [translateWalshIndex_mixedPair]; simp
  have e1m : translateWalshIndex (-Operator.axisVector 1) (mixedPairFinset (m, n))
      = mixedPairFinset (m - 1, n) := by
    rw [translateWalshIndex_mixedPair]; simp [sub_eq_add_neg]
  rw [loweringCoefficient_eq, Fin.sum_univ_two, e0p, e0m, e1p, e1m,
    hx _ (not_isType112_toggle_vertical_mixedPair (m + 1) n),
    hx _ (not_isType112_toggle_vertical_mixedPair (m - 1) n)]
  by_cases hm : m = 0
  · subst hm
    rw [toggle_horizontal_mixedPair_zero, toggle_horizontal_mixedPair_zero,
      hx _ (not_isType112_of_card_ne (S := {(Axis.vertical, n + 1)}) (by simp)),
      hx _ (not_isType112_of_card_ne (S := {(Axis.vertical, n - 1)}) (by simp)),
      hx _ (not_isType112_tripleToFinset_diag 0 (n + 1)),
      hx _ (not_isType112_tripleToFinset_diag 0 (n - 1))]
    ring
  · rw [toggle_horizontal_mixedPair_of_ne hm, toggle_horizontal_mixedPair_of_ne hm]
    ring

/-! ## The density argument -/

/-- The finite type-`112` Walsh polynomials. -/
def type112Span : Submodule ℂ WalshL2 :=
  Submodule.span ℂ (Set.range fun T : Type112Index => walshL2 T.1)

/-- The complete type-`112` synthesis lands in the closure of the finite
type-`112` Walsh polynomials: this is the density half of the closure
argument. -/
theorem type112WalshSynthesis_mem_topologicalClosure (c : ℓ²(Type112Index, ℂ)) :
    type112WalshSynthesis c ∈ type112Span.topologicalClosure := by
  let V : Type112Index → ℂ →ₗᵢ[ℂ] WalshL2 := fun S =>
    LinearIsometry.toSpanSingleton ℂ WalshL2
      (orthonormal_type112WalshFamily.1 S)
  let U : Submodule ℂ WalshL2 := ⨆ S, LinearMap.range (V S).toLinearMap
  have hrange : type112WalshSynthesis c ∈ U.topologicalClosure := by
    have hrange' : type112WalshSynthesis c ∈
        LinearMap.range
          orthonormal_type112WalshFamily.orthogonalFamily.linearIsometry.toLinearMap :=
      ⟨c, rfl⟩
    rw [OrthogonalFamily.range_linearIsometry] at hrange'
    exact hrange'
  have hU : U ≤ type112Span := by
    refine iSup_le fun S => ?_
    rintro _ ⟨a, rfl⟩
    have : a • walshL2 S.1 ∈ type112Span :=
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨S, rfl⟩)
    exact this
  exact Submodule.topologicalClosure_mono hU hrange

/-- **The closure argument.**  Two continuous linear functionals that agree on
every type-`112` Walsh character agree on the whole closed type-`112` sector. -/
theorem eq_of_mem_type112Closure {f g : WalshL2 →L[ℂ] ℂ}
    (h : ∀ T : Type112Index, f (walshL2 T.1) = g (walshL2 T.1))
    {x : WalshL2} (hx : x ∈ type112Span.topologicalClosure) : f x = g x := by
  have hker : type112Span ≤ LinearMap.ker (f - g) := by
    rw [type112Span, Submodule.span_le]
    rintro _ ⟨T, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_sub',
      Pi.sub_apply, sub_eq_zero]
    exact h T
  have hclosed : IsClosed ((LinearMap.ker (f - g) : Submodule ℂ WalshL2) : Set WalshL2) :=
    ContinuousLinearMap.isClosed_ker (f - g)
  have hmem := Submodule.topologicalClosure_minimal type112Span hker hclosed hx
  have : (f - g) x = 0 := hmem
  simpa [sub_eq_zero] using this

/-- Everything carried by the type-`112` indices and lying in the closed sector
is type-`112` supported; the sector condition is closed. -/
theorem isType112Supported_of_mem_topologicalClosure {x : WalshL2}
    (hx : x ∈ type112Span.topologicalClosure) : IsType112Supported x := by
  intro S hS
  have h : ∀ T : Type112Index,
      (innerSL ℂ (walshL2 S)) (walshL2 T.1) = (0 : WalshL2 →L[ℂ] ℂ) (walshL2 T.1) := by
    intro T
    simpa using isType112Supported_walshL2 T S hS
  simpa [walshCoefficientAt] using eq_of_mem_type112Closure h hx

/-! ## The `L²` forms of (D2a) and (D2b) -/

/-- The lowering functional `x ↦ (D* x)_S`, as a continuous linear functional. -/
def loweringFunctional (p : Fin 2 → ℝ) (S : Finset LineIndex) : WalshL2 →L[ℂ] ℂ :=
  innerSL ℂ (concreteFiberA p (walshL2 S))

@[simp] theorem loweringFunctional_apply (p : Fin 2 → ℝ) (S : Finset LineIndex)
    (x : WalshL2) : loweringFunctional p S x = loweringCoefficient p x S := rfl

/-- One Walsh coefficient, as a continuous linear functional. -/
def walshFunctional (S : Finset LineIndex) : WalshL2 →L[ℂ] ℂ :=
  innerSL ℂ (walshL2 S)

@[simp] theorem walshFunctional_apply (S : Finset LineIndex) (x : WalshL2) :
    walshFunctional S x = walshCoefficientAt x S := rfl

/-- **(D2a) on the closed type-`112` sector, by density.**  This is the closure
argument in the form the manuscript uses it: both sides are continuous linear
functionals, they agree on every finite type-`112` Walsh polynomial, hence they
agree on the closure of those polynomials. -/
theorem loweringCoefficient_rowPair_of_mem_closure (p : Fin 2 → ℝ) {x : WalshL2}
    (hx : x ∈ type112Span.topologicalClosure) (m m' : ℤ) :
    loweringCoefficient p x (rowPairFinset (m, m')) =
      ((2 : ℂ)⁻¹ * Complex.exp (-Complex.I * p 1)) *
          walshCoefficientAt x (tripleToFinset (m + 1, m' + 1, 0)) -
        ((2 : ℂ)⁻¹ * Complex.exp (Complex.I * p 1)) *
          walshCoefficientAt x (tripleToFinset (m - 1, m' - 1, 0)) := by
  have h : ∀ T : Type112Index,
      loweringFunctional p (rowPairFinset (m, m')) (walshL2 T.1) =
        (((2 : ℂ)⁻¹ * Complex.exp (-Complex.I * p 1)) •
              walshFunctional (tripleToFinset (m + 1, m' + 1, 0)) -
            ((2 : ℂ)⁻¹ * Complex.exp (Complex.I * p 1)) •
              walshFunctional (tripleToFinset (m - 1, m' - 1, 0))) (walshL2 T.1) := by
    intro T
    simpa using
      loweringCoefficient_rowPair_of_supported p (isType112Supported_walshL2 T) m m'
  simpa using eq_of_mem_type112Closure h hx

/-- **(D2b) on the closed type-`112` sector, by density.** -/
theorem loweringCoefficient_mixedPair_of_mem_closure (p : Fin 2 → ℝ) {x : WalshL2}
    (hx : x ∈ type112Span.topologicalClosure) (m n : ℤ) :
    loweringCoefficient p x (mixedPairFinset (m, n)) =
      ((2 : ℂ)⁻¹ * Complex.exp (-Complex.I * p 0)) *
          walshCoefficientAt x (tripleToFinset (m, 0, n + 1)) -
        ((2 : ℂ)⁻¹ * Complex.exp (Complex.I * p 0)) *
          walshCoefficientAt x (tripleToFinset (m, 0, n - 1)) := by
  have h : ∀ T : Type112Index,
      loweringFunctional p (mixedPairFinset (m, n)) (walshL2 T.1) =
        (((2 : ℂ)⁻¹ * Complex.exp (-Complex.I * p 0)) •
              walshFunctional (tripleToFinset (m, 0, n + 1)) -
            ((2 : ℂ)⁻¹ * Complex.exp (Complex.I * p 0)) •
              walshFunctional (tripleToFinset (m, 0, n - 1))) (walshL2 T.1) := by
    intro T
    simpa using
      loweringCoefficient_mixedPair_of_supported p (isType112Supported_walshL2 T) m n
  simpa using eq_of_mem_type112Closure h hx

/-! ## The degree-two Finset sectors -/

theorem isType11Index_rowPairFinset {m m' : ℤ} (hne : m ≠ m') :
    IsType11Index (rowPairFinset (m, m')) := by
  constructor
  · simp [rowPairFinset, hne]
  · intro l hl
    simp only [rowPairFinset, Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl <;> rfl

theorem isType12Index_mixedPairFinset (m n : ℤ) :
    IsType12Index (mixedPairFinset (m, n)) := by
  constructor
  · simp [mixedPairFinset]
  · have hfilter : (mixedPairFinset (m, n)).filter
        (fun l => l.1 = Axis.horizontal) =
        ({(Axis.horizontal, m)} : Finset LineIndex) := by
      ext l
      obtain ⟨i, j⟩ := l
      cases i <;> simp [mixedPairFinset]
    rw [hfilter]
    simp

/-- The two-row Walsh index is the row pair of its ordered coordinates. -/
theorem rowPairFinset_type11RawIndex (T : Type11Index) :
    rowPairFinset (type11RawIndex T 0, type11RawIndex T 1) = T.1 := by
  have h := orderedType11Equiv.apply_symm_apply T
  have h1 : orderedType11Lines (orderedType11Equiv.symm T) = T.1 :=
    congrArg Subtype.val h
  exact h1

/-- **(D2a) for an arbitrary square-summable type-`112` coefficient.**  This is
the `L²` form of `Manhattan.Glue.frequency_D2a`: the complete two-row component
of `D₂*` is one signed lattice step in both row indices, with the column index
of the input pinned to the origin. -/
theorem type112DStarTwoRow_eq (p : Fin 2 → ℝ) (c : ℓ²(Type112Index, ℂ))
    (T : Type11Index) :
    type112DStarTwoRow p c T =
      ((2 : ℂ)⁻¹ * Complex.exp (-Complex.I * p 1)) *
          type112CoefficientAt c
            (tripleToFinset (type11RawIndex T 0 + 1, type11RawIndex T 1 + 1, 0)) -
        ((2 : ℂ)⁻¹ * Complex.exp (Complex.I * p 1)) *
          type112CoefficientAt c
            (tripleToFinset (type11RawIndex T 0 - 1, type11RawIndex T 1 - 1, 0)) := by
  rw [type112DStarTwoRow_eq_loweringCoefficient, ← rowPairFinset_type11RawIndex T,
    loweringCoefficient_rowPair_of_mem_closure p
      (type112WalshSynthesis_mem_topologicalClosure c)]
  simp only [walshCoefficientAt, inner_walshL2_type112WalshSynthesis]

/-- **(D2b) for an arbitrary square-summable type-`112` coefficient.**  This is
the `L²` form of `Manhattan.Glue.frequency_D2b`. -/
theorem type112DStarMixed_eq (p : Fin 2 → ℝ) (c : ℓ²(Type112Index, ℂ))
    (m n : ℤ) :
    type112DStarMixed p c ⟨mixedPairFinset (m, n), isType12Index_mixedPairFinset m n⟩ =
      ((2 : ℂ)⁻¹ * Complex.exp (-Complex.I * p 0)) *
          type112CoefficientAt c (tripleToFinset (m, 0, n + 1)) -
        ((2 : ℂ)⁻¹ * Complex.exp (Complex.I * p 0)) *
          type112CoefficientAt c (tripleToFinset (m, 0, n - 1)) := by
  rw [type112DStarMixed_eq_loweringCoefficient]
  rw [loweringCoefficient_mixedPair_of_mem_closure p
      (type112WalshSynthesis_mem_topologicalClosure c)]
  simp only [walshCoefficientAt, inner_walshL2_type112WalshSynthesis]

end

end Manhattan.Glue
