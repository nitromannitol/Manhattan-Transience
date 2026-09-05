import Manhattan.Walsh.Coefficients
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Completeness of the infinite Walsh family

The finite-sign expansion is elementary, but passing to the countable product
requires the cylinder-density argument omitted at `manuscript.tex:711-715`.
The exact remaining interface is isolated here; see erratum E-004.
-/

namespace Manhattan

open MeasureTheory Set
open scoped BigOperators ENNReal

noncomputable section

private def walshAtomCoefficient (s : Finset LineIndex) (η : Environment) :
    WalshCoefficient :=
  ∑ T ∈ s.powerset, Finsupp.single T
    (((2 : ℂ)⁻¹ ^ s.card) * ∏ l ∈ T, coordinateCharacter l η)

private theorem walshPolynomial_atomCoefficient (s : Finset LineIndex)
    (η ω : Environment) :
    walshPolynomial (walshAtomCoefficient s η) ω =
      if ∀ l ∈ s, ω l = η l then 1 else 0 := by
  classical
  rw [walshAtomCoefficient]
  rw [walshPolynomial_finset_sum]
  simp only [walshPolynomial_single]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  have hexpand :
      ∑ T ∈ s.powerset,
          (∏ l ∈ T, coordinateCharacter l η) * walshCharacter T ω =
        ∏ l ∈ s, (coordinateCharacter l η * coordinateCharacter l ω + 1) := by
    rw [Finset.prod_add]
    simp only [Finset.prod_const_one, mul_one, walshCharacter]
    apply Finset.sum_congr rfl
    intro T hT
    rw [← Finset.prod_mul_distrib]
  rw [hexpand, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  have hfactor (l : LineIndex) :
      (2 : ℂ)⁻¹ *
          (coordinateCharacter l η * coordinateCharacter l ω + 1) =
        if ω l = η l then 1 else 0 := by
    cases hη : η l <;> cases hω : ω l <;>
      simp [coordinateCharacter, orientationCharacter, Orientation.sign, hη, hω] <;>
      norm_num
  simp_rw [hfactor]
  by_cases hagree : ∀ l ∈ s, ω l = η l
  · rw [if_pos hagree]
    exact Finset.prod_eq_one fun l hl => if_pos (hagree l hl)
  · rw [if_neg hagree]
    push_neg at hagree
    obtain ⟨l, hl, hne⟩ := hagree
    exact Finset.prod_eq_zero hl (if_neg hne)

private def extendCylinderPoint {s : Finset LineIndex}
    (σ : (l : s) → Orientation) : Environment :=
  fun l => if hl : l ∈ s then σ ⟨l, hl⟩ else .negative

private theorem agree_extendCylinderPoint_iff (s : Finset LineIndex)
    (σ : (l : s) → Orientation) (ω : Environment) :
    (∀ l ∈ s, ω l = extendCylinderPoint σ l) ↔ s.restrict ω = σ := by
  constructor
  · intro h
    funext l
    simpa [Finset.restrict, extendCylinderPoint, l.property] using h l l.property
  · intro h l hl
    have hl' := congrFun h ⟨l, hl⟩
    simpa [Finset.restrict, extendCylinderPoint, hl] using hl'

private noncomputable def walshCylinderCoefficient (s : Finset LineIndex)
    (A : Set ((l : s) → Orientation)) : WalshCoefficient := by
  classical
  exact ∑ σ : (l : s) → Orientation,
    if σ ∈ A then walshAtomCoefficient s (extendCylinderPoint σ) else 0

private theorem walshPolynomial_cylinderCoefficient (s : Finset LineIndex)
    (A : Set ((l : s) → Orientation)) (ω : Environment) :
    walshPolynomial (walshCylinderCoefficient s A) ω =
      A.indicator (fun _ => (1 : ℂ)) (s.restrict ω) := by
  classical
  rw [walshCylinderCoefficient, walshPolynomial_finset_sum]
  simp only [walshPolynomial_ite, walshPolynomial_atomCoefficient,
    walshPolynomial_zero]
  simp_rw [agree_extendCylinderPoint_iff]
  by_cases hA : s.restrict ω ∈ A
  · rw [Set.indicator_of_mem hA]
    rw [Finset.sum_eq_single (s.restrict ω)]
    · simp [hA]
    · intro σ _ hne
      by_cases hσ : σ ∈ A <;> simp [hσ, Ne.symm hne]
    · simp
  · rw [Set.indicator_of_notMem hA]
    apply Finset.sum_eq_zero
    intro σ _
    by_cases hσ : σ ∈ A <;> simp [hσ]
    exact fun heq => hA (heq ▸ hσ)

private theorem cylinderIndicator_mem_walshSpan (s : Finset LineIndex)
    (A : Set ((l : s) → Orientation)) (hA : MeasurableSet A) (c : ℂ) :
    indicatorConstLp 2 hA.cylinder (measure_ne_top environmentLaw _) c ∈
      Submodule.span ℂ (Set.range walshL2) := by
  classical
  let d : WalshCoefficient := c • walshCylinderCoefficient s A
  have hEq : indicatorConstLp 2 hA.cylinder (measure_ne_top environmentLaw _) c =
      walshSynthesis d := by
    apply Lp.ext
    refine indicatorConstLp_coeFn.trans ?_
    have hpoint : (cylinder s A).indicator (fun _ => c) = walshPolynomial d := by
      funext ω
      simp only [d, walshPolynomial_smul, walshPolynomial_cylinderCoefficient,
        Set.indicator_apply, mem_cylinder]
      by_cases hω : s.restrict ω ∈ A <;> simp [hω]
    exact hpoint.eventuallyEq.trans (coeFn_walshSynthesis d).symm
  rw [hEq]
  rw [← Finsupp.range_linearCombination (R := ℂ) (v := walshL2)]
  exact ⟨d, rfl⟩

/-- The closed linear span of all finite Walsh characters. -/
noncomputable def walshClosedSpan : Submodule ℂ WalshL2 :=
  Submodule.topologicalClosure (Submodule.span ℂ (Set.range walshL2))

/-- The finite Walsh characters are complete in the product `L²` space.

The intended proof expands every finite cylinder indicator into characters,
uses `Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite` for measurable
cylinders, and finishes by `Lp.induction`.
-/
theorem walsh_complete : walshClosedSpan = ⊤
  := by
  let cylinders : Set (Set Environment) :=
    measurableCylinders (fun _ : LineIndex => Orientation)
  have hdense : environmentLaw.MeasureDense cylinders :=
    Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite
      environmentLaw
      isSetAlgebra_measurableCylinders
      (generateFrom_measurableCylinders
        (α := fun _ : LineIndex => Orientation)).symm
  apply Submodule.eq_top_iff'.2
  intro f
  have htwo : (2 : ℝ≥0∞) ≠ ∞ := by norm_num
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨htwo⟩
  refine Lp.induction htwo
    (motive := fun g : WalshL2 => g ∈ walshClosedSpan) ?_ ?_
    (Submodule.isClosed_topologicalClosure _) f
  · intro c s hs hμs
    have happrox := hdense.indicatorConstLp_subset_closure (2 : ℝ≥0∞) c
      ⟨s, hs, hμs.ne, rfl⟩
    apply (Submodule.isClosed_topologicalClosure _).closure_subset_iff.2 _ happrox
    rintro _ ⟨t, ht, htfin, rfl⟩
    obtain ⟨I, A, hA, rfl⟩ := (mem_measurableCylinders _).1 ht
    exact Submodule.le_topologicalClosure _
      (cylinderIndicator_mem_walshSpan I A hA c)
  · intro g h hgp hhp _ hg hh
    exact Submodule.add_mem _ hg hh

/-- The complete Finset-indexed Walsh Hilbert basis of `L²(P)`. -/
noncomputable def walshBasis : HilbertBasis (Finset LineIndex) ℂ WalshL2 :=
  HilbertBasis.mk orthonormal_walshL2 <| by
    rw [← walshClosedSpan, walsh_complete]

@[simp] theorem walshBasis_apply (S : Finset LineIndex) :
    walshBasis S = walshL2 S := by
  unfold walshBasis
  rw [HilbertBasis.coe_mk]

/-- Full Walsh synthesis on square-summable Finset-indexed coefficients. -/
noncomputable def walshSynthesisL2 :
    ℓ²(Finset LineIndex, ℂ) ≃ₗᵢ[ℂ] WalshL2 :=
  walshBasis.repr.symm

/-- The complete form of the factorial-free isometry (17). -/
theorem norm_walshSynthesisL2 (c : ℓ²(Finset LineIndex, ℂ)) :
    ‖walshSynthesisL2 c‖ = ‖c‖ := by
  exact walshSynthesisL2.norm_map c

end

end Manhattan
