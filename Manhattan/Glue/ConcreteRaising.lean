import Manhattan.Model.LowDegree

/-!
# Lemma 5.1 in the concrete model: raising and lowering

This module proves, for the actual operator `concreteFiberEnvironment.fiberA`,
the splitting `A = D - D*` of `manuscript.tex:735-737` together with the
explicit coefficient formula (45) of `manuscript.tex:1179-1188`.

indexes Walsh chaos by finite sets of distinct line indices.  In
that convention the paper's symmetrization factor `1/(n+1)` and the sum over
the `n+1` slots of an ordered tuple are replaced by the single sum over the two
possible types of the appended line: raising appends the line of type `i`
through the origin, so the slot which carries the new index is determined by
its type.  The projection `Pi_{n+1}` of the manuscript is built into the
Finset convention, since `insert` cannot create a repeated line index.

Paper: `manuscript.tex:719-758`, `manuscript.tex:793-822`,
`manuscript.tex:1176-1200`.
-/

open ComplexConjugate InnerProductSpace MeasureTheory
open scoped BigOperators ComplexConjugate InnerProduct symmDiff

namespace Manhattan.Glue

noncomputable section

/-- Classical decidability, local to this file: the statements here are analytic, not computational. -/
local instance concreteRaisingPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-! ### Walsh coordinate projections -/

/-- The closed linear span of the Walsh characters whose index set satisfies
`P`. -/
def walshSubspace (P : Finset LineIndex → Prop) : Submodule ℂ WalshL2 :=
  (Submodule.span ℂ {x | ∃ S, P S ∧ x = walshL2 S}).topologicalClosure

instance walshSubspace_hasOrthogonalProjection (P : Finset LineIndex → Prop) :
    (walshSubspace P).HasOrthogonalProjection := by
  haveI : CompleteSpace (walshSubspace P) :=
    (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  infer_instance

/-- The orthogonal projection onto the Walsh characters selected by `P`. -/
def walshProjection (P : Finset LineIndex → Prop) : WalshL2 →L[ℂ] WalshL2 :=
  (walshSubspace P).starProjection

theorem walshL2_mem_walshSubspace {P : Finset LineIndex → Prop}
    {S : Finset LineIndex} (hS : P S) : walshL2 S ∈ walshSubspace P :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨S, hS, rfl⟩)

theorem walshL2_mem_walshSubspace_orthogonal {P : Finset LineIndex → Prop}
    {S : Finset LineIndex} (hS : ¬ P S) : walshL2 S ∈ (walshSubspace P)ᗮ := by
  have hle : walshSubspace P ≤ (Submodule.span ℂ {walshL2 S})ᗮ := by
    refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_orthogonal _)
    rw [Submodule.span_le]
    rintro _ ⟨T, hT, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal]
    intro u hu
    rw [Submodule.mem_span_singleton] at hu
    obtain ⟨a, rfl⟩ := hu
    rw [inner_smul_left, inner_walshL2, if_neg (fun h : S = T => hS (h ▸ hT))]
    simp
  rw [Submodule.mem_orthogonal]
  intro u hu
  have hu' := hle hu
  rw [Submodule.mem_orthogonal] at hu'
  have h0 := hu' (walshL2 S) (Submodule.mem_span_singleton_self _)
  rw [← inner_conj_symm, h0, map_zero]

@[simp] theorem walshProjection_walshL2 (P : Finset LineIndex → Prop)
    (S : Finset LineIndex) :
    walshProjection P (walshL2 S) = if P S then walshL2 S else 0 := by
  by_cases h : P S
  · rw [if_pos h]
    exact Submodule.starProjection_eq_self_iff.mpr (walshL2_mem_walshSubspace h)
  · rw [if_neg h]
    refine Submodule.eq_starProjection_of_mem_orthogonal (Submodule.zero_mem _) ?_
    simpa using walshL2_mem_walshSubspace_orthogonal h

theorem walshProjection_isSelfAdjoint (P : Finset LineIndex → Prop) :
    IsSelfAdjoint (walshProjection P) :=
  isSelfAdjoint_starProjection _

@[simp] theorem walshProjection_adjoint (P : Finset LineIndex → Prop) :
    (walshProjection P)† = walshProjection P :=
  walshProjection_isSelfAdjoint P

/-! ### An extensionality principle on the Walsh basis -/

theorem walshL2_span_dense :
    Dense (Submodule.span ℂ (Set.range walshL2) : Set WalshL2) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  exact walsh_complete

theorem walshL2_ext_op {T U : WalshL2 →L[ℂ] WalshL2}
    (h : ∀ S : Finset LineIndex, T (walshL2 S) = U (walshL2 S)) : T = U := by
  refine ContinuousLinearMap.ext_on walshL2_span_dense ?_
  rintro _ ⟨S, rfl⟩
  exact h S

/-! ### The creation and annihilation halves of a sign multiplication

Multiplication by `omega(0,i)` adds the line of type `i` through the origin
when it is absent and removes it when it is present (`manuscript.tex:733-737`).
The two halves are the paper's `D` and `D*` before the phase factors. -/

/-- The degree-raising half of multiplication by the sign at the origin. -/
def originRaise (i : Fin 2) : WalshL2 →L[ℂ] WalshL2 :=
  walshProjection (fun S => originLine i ∈ S) ∘L originSignMultiplier i

/-- The degree-lowering half of multiplication by the sign at the origin. -/
def originLower (i : Fin 2) : WalshL2 →L[ℂ] WalshL2 :=
  walshProjection (fun S => originLine i ∉ S) ∘L originSignMultiplier i

@[simp] theorem originRaise_walshL2 (i : Fin 2) (S : Finset LineIndex) :
    originRaise i (walshL2 S) =
      if originLine i ∈ S then 0 else walshL2 (insert (originLine i) S) := by
  rw [originRaise, ContinuousLinearMap.comp_apply,
    originSignMultiplier_walshL2_public, toggleOriginWalshIndex_eq_ite]
  by_cases h : originLine i ∈ S
  · rw [if_pos h, if_pos h]
    simp only [walshProjection_walshL2]
    exact if_neg (Finset.notMem_erase _ _)
  · rw [if_neg h, if_neg h]
    simp only [walshProjection_walshL2]
    exact if_pos (Finset.mem_insert_self _ _)

@[simp] theorem originLower_walshL2 (i : Fin 2) (S : Finset LineIndex) :
    originLower i (walshL2 S) =
      if originLine i ∈ S then walshL2 (S.erase (originLine i)) else 0 := by
  rw [originLower, ContinuousLinearMap.comp_apply,
    originSignMultiplier_walshL2_public, toggleOriginWalshIndex_eq_ite]
  by_cases h : originLine i ∈ S
  · rw [if_pos h, if_pos h]
    simp only [walshProjection_walshL2]
    exact if_pos (Finset.notMem_erase _ _)
  · rw [if_neg h, if_neg h]
    simp only [walshProjection_walshL2]
    exact if_neg (by simp)

/-- Equation (18) at the operator level: multiplication by one origin sign is
the sum of its raising and lowering halves. -/
theorem originRaise_add_originLower (i : Fin 2) :
    originRaise i + originLower i = originSignMultiplier i := by
  refine walshL2_ext_op fun S => ?_
  rw [ContinuousLinearMap.add_apply, originRaise_walshL2, originLower_walshL2,
    originSignMultiplier_walshL2_public, toggleOriginWalshIndex_eq_ite]
  by_cases h : originLine i ∈ S <;> simp [h]

/-- The two halves are mutually adjoint. -/
@[simp] theorem originRaise_adjoint (i : Fin 2) :
    (originRaise i)† = originLower i := by
  rw [originRaise, ContinuousLinearMap.adjoint_comp, walshProjection_adjoint,
    originSignMultiplier_adjoint]
  refine walshL2_ext_op fun S => ?_
  rw [ContinuousLinearMap.comp_apply, originLower_walshL2]
  simp only [walshProjection_walshL2]
  by_cases h : originLine i ∈ S
  · rw [if_pos h, if_pos h, originSignMultiplier_walshL2_public,
      toggleOriginWalshIndex_eq_ite, if_pos h]
  · rw [if_neg h, if_neg h, map_zero]

@[simp] theorem originLower_adjoint (i : Fin 2) :
    (originLower i)† = originRaise i := by
  rw [← originRaise_adjoint, ContinuousLinearMap.adjoint_adjoint]

/-! ### Translations along a line fix that line -/

theorem lineTranslation_axis_originLine (i : Fin 2) (sign : ℤ) :
    lineTranslation (latticeToSite (sign • Operator.axisVector i)) (originLine i) =
      originLine i := by
  fin_cases i <;>
    simp [lineTranslation, latticeToSite, transverseCoordinate, Operator.axisVector,
      originLine, finAxis]

theorem originLine_mem_translateWalshIndex (i : Fin 2) (sign : ℤ)
    (S : Finset LineIndex) :
    originLine i ∈ translateWalshIndex (sign • Operator.axisVector i) S ↔
      originLine i ∈ S := by
  have he : (lineTranslation
      (latticeToSite (sign • Operator.axisVector i))).symm (originLine i) =
      originLine i := by
    rw [Equiv.symm_apply_eq, lineTranslation_axis_originLine]
  rw [translateWalshIndex, Finset.mem_map_equiv, he]

theorem translateWalshIndex_axis_insert (i : Fin 2) (sign : ℤ)
    (S : Finset LineIndex) :
    translateWalshIndex (sign • Operator.axisVector i) (insert (originLine i) S) =
      insert (originLine i)
        (translateWalshIndex (sign • Operator.axisVector i) S) := by
  rw [translateWalshIndex, translateWalshIndex, Finset.map_insert]
  congr 1
  exact lineTranslation_axis_originLine i sign

theorem translateWalshIndex_axis_erase (i : Fin 2) (sign : ℤ)
    (S : Finset LineIndex) :
    translateWalshIndex (sign • Operator.axisVector i) (S.erase (originLine i)) =
      (translateWalshIndex (sign • Operator.axisVector i) S).erase (originLine i) := by
  rw [translateWalshIndex, translateWalshIndex, Finset.map_erase]
  congr 1
  exact lineTranslation_axis_originLine i sign

theorem originLower_comp_environmentShift (i : Fin 2) (sign : ℤ) :
    originLower i ∘L environmentShift (sign • Operator.axisVector i) =
      environmentShift (sign • Operator.axisVector i) ∘L originLower i := by
  refine walshL2_ext_op fun S => ?_
  simp only [ContinuousLinearMap.comp_apply, environmentShift_walshL2_public,
    originLower_walshL2]
  by_cases h : originLine i ∈ S
  · rw [if_pos ((originLine_mem_translateWalshIndex i sign S).mpr h), if_pos h,
      environmentShift_walshL2_public, translateWalshIndex_axis_erase]
  · rw [if_neg (fun hc => h ((originLine_mem_translateWalshIndex i sign S).mp hc)),
      if_neg h, map_zero]

/-! ### The concrete raising and lowering operators -/

theorem fiberSkewTerm_walshL2 (p : Fin 2 -> Real) (i : Fin 2)
    (S : Finset LineIndex) :
    fiberSkewTerm p i (walshL2 S) =
      Complex.exp (Complex.I * p i) •
          walshL2 (translateWalshIndex (Operator.axisVector i) S) -
        Complex.exp (-Complex.I * p i) •
          walshL2 (translateWalshIndex (-Operator.axisVector i) S) := by
  rw [fiberSkewTerm, phasedShift_adjoint, phasedShift]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    environmentShift_walshL2_public]

/-- The direction-`i` summand of the paper's raising operator `D`. -/
def walshRaiseDir (p : Fin 2 -> Real) (i : Fin 2) : WalshL2 →L[ℂ] WalshL2 :=
  (2 : ℂ)⁻¹ • (originRaise i ∘L fiberSkewTerm p i)

/-- The direction-`i` summand of the paper's lowering operator `D*`. -/
def walshLowerDir (p : Fin 2 -> Real) (i : Fin 2) : WalshL2 →L[ℂ] WalshL2 :=
  -((2 : ℂ)⁻¹ • (originLower i ∘L fiberSkewTerm p i))

/-- The paper's raising operator `D` on the whole Walsh space. -/
def walshRaise (p : Fin 2 -> Real) : WalshL2 →L[ℂ] WalshL2 :=
  ∑ i, walshRaiseDir p i

/-- The paper's lowering operator `D*` on the whole Walsh space. -/
def walshLower (p : Fin 2 -> Real) : WalshL2 →L[ℂ] WalshL2 :=
  ∑ i, walshLowerDir p i

/-- **Lemma 5.1, splitting half** in the concrete model: the actual skew part
of the Fourier fiber is `D - D*` (`manuscript.tex:735-737`). -/
theorem concreteFiberA_eq_walshRaise_sub_walshLower (p : Fin 2 -> Real) :
    concreteFiberA p = walshRaise p - walshLower p := by
  rw [concreteFiberA, walshRaise, walshLower, ← Finset.sum_sub_distrib,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [walshRaiseDir, walshLowerDir, sub_neg_eq_add, ← smul_add,
    ← ContinuousLinearMap.add_comp, originRaise_add_originLower]

/-- The same statement for the bundled fiber environment.
The unbundled
`Manhattan.Glue.concreteFiberA_eq_walshRaise_sub_walshLower` is the one that is
used. -/
theorem fiberA_eq_walshRaise_sub_walshLower (p : Fin 2 -> Real) :
    concreteFiberEnvironment.fiberA p = walshRaise p - walshLower p :=
  concreteFiberA_eq_walshRaise_sub_walshLower p

/-- **Lemma 5.1, adjoint half**: `D*` really is the adjoint of `D`. -/
theorem walshLower_eq_adjoint_walshRaise (p : Fin 2 -> Real) :
    walshLower p = (walshRaise p)† := by
  rw [walshRaise, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [walshRaiseDir, walshLowerDir, map_smulₛₗ, ContinuousLinearMap.adjoint_comp,
    originRaise_adjoint, fiberSkewTerm_adjoint]
  have hhalf : (starRingEnd ℂ) ((2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ := by
    rw [map_inv₀, map_ofNat]
  rw [hhalf, ContinuousLinearMap.neg_comp, ← smul_neg]
  congr 1
  rw [fiberSkewTerm, phasedShift_adjoint, phasedShift,
    ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub,
    ContinuousLinearMap.smul_comp, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_smul]
  have h1 := originLower_comp_environmentShift i 1
  have h2 := originLower_comp_environmentShift i (-1)
  simp only [one_smul, neg_smul] at h1 h2
  rw [h1, h2]

/-! ### The exact Finset coefficient formula

This is equation (45) of `manuscript.tex:1181-1188` in the Finset convention of
The appended line index is the line of type `i` through the
origin, so the paper's sum over the `n+1` slots of a symmetric tuple becomes the
sum over the two types `i` for which that line occurs in the output index set;
the manuscript's symmetrization factor `1/(n+1)` disappears with the `n!` of
(17). -/

private theorem conj_exp_I_mul (x : ℝ) :
    (starRingEnd ℂ) (Complex.exp (Complex.I * x)) =
      Complex.exp (-Complex.I * x) := by
  rw [← Complex.exp_conj]
  congr 1
  simp

private theorem conj_exp_neg_I_mul (x : ℝ) :
    (starRingEnd ℂ) (Complex.exp (-Complex.I * x)) =
      Complex.exp (Complex.I * x) := by
  rw [← Complex.exp_conj]
  congr 1
  simp

/-- **Lemma 5.1, coefficient formula.**  The Walsh coefficient of the
direction-`i` raising operator at an index set `T` containing the origin line of
type `i` is the phase difference of the two shifted coefficients at
`T \ {(i,0)}`; it vanishes when `T` does not contain that line. -/
theorem inner_walshL2_walshRaiseDir (p : Fin 2 -> Real) (i : Fin 2)
    (T : Finset LineIndex) (x : WalshL2) :
    inner ℂ (walshL2 T) (walshRaiseDir p i x) =
      if originLine i ∈ T then
        (2 : ℂ)⁻¹ *
          (Complex.exp (Complex.I * p i) *
              inner ℂ (walshL2 (translateWalshIndex (-Operator.axisVector i)
                (T.erase (originLine i)))) x -
            Complex.exp (-Complex.I * p i) *
              inner ℂ (walshL2 (translateWalshIndex (Operator.axisVector i)
                (T.erase (originLine i)))) x)
      else 0 := by
  have hadj : ((originRaise i ∘L fiberSkewTerm p i)† : WalshL2 →L[ℂ] WalshL2)
      (walshL2 T) = -(fiberSkewTerm p i) (originLower i (walshL2 T)) := by
    rw [ContinuousLinearMap.adjoint_comp, originRaise_adjoint, fiberSkewTerm_adjoint]
    rfl
  rw [walshRaiseDir, ContinuousLinearMap.smul_apply, inner_smul_right,
    ← ContinuousLinearMap.adjoint_inner_left, hadj]
  by_cases h : originLine i ∈ T
  · rw [if_pos h, originLower_walshL2, if_pos h, fiberSkewTerm_walshL2,
      inner_neg_left, inner_sub_left, inner_smul_left, inner_smul_left,
      conj_exp_I_mul, conj_exp_neg_I_mul]
    ring
  · rw [if_neg h, originLower_walshL2, if_neg h, map_zero, neg_zero,
      inner_zero_left, mul_zero]

/-- The adjoint coefficient formula: the direction-`i` lowering operator. -/
theorem inner_walshL2_walshLowerDir (p : Fin 2 -> Real) (i : Fin 2)
    (T : Finset LineIndex) (x : WalshL2) :
    inner ℂ (walshL2 T) (walshLowerDir p i x) =
      if originLine i ∈ T then 0
      else
        -((2 : ℂ)⁻¹ *
          (Complex.exp (Complex.I * p i) *
              inner ℂ (walshL2 (translateWalshIndex (-Operator.axisVector i)
                (insert (originLine i) T))) x -
            Complex.exp (-Complex.I * p i) *
              inner ℂ (walshL2 (translateWalshIndex (Operator.axisVector i)
                (insert (originLine i) T))) x)) := by
  have hadj : ((originLower i ∘L fiberSkewTerm p i)† : WalshL2 →L[ℂ] WalshL2)
      (walshL2 T) = -(fiberSkewTerm p i) (originRaise i (walshL2 T)) := by
    rw [ContinuousLinearMap.adjoint_comp, originLower_adjoint, fiberSkewTerm_adjoint]
    rfl
  rw [walshLowerDir, ContinuousLinearMap.neg_apply, inner_neg_right,
    ContinuousLinearMap.smul_apply, inner_smul_right,
    ← ContinuousLinearMap.adjoint_inner_left, hadj]
  by_cases h : originLine i ∈ T
  · rw [if_pos h, originRaise_walshL2, if_pos h, map_zero, neg_zero,
      inner_zero_left, mul_zero, neg_zero]
  · rw [if_neg h, originRaise_walshL2, if_neg h, fiberSkewTerm_walshL2,
      inner_neg_left, inner_sub_left, inner_smul_left, inner_smul_left,
      conj_exp_I_mul, conj_exp_neg_I_mul]
    ring

/-- Summing the two directions gives the full raising coefficient. -/
theorem inner_walshL2_walshRaise (p : Fin 2 -> Real)
    (T : Finset LineIndex) (x : WalshL2) :
    inner ℂ (walshL2 T) (walshRaise p x) =
      ∑ i : Fin 2,
        if originLine i ∈ T then
          (2 : ℂ)⁻¹ *
            (Complex.exp (Complex.I * p i) *
                inner ℂ (walshL2 (translateWalshIndex (-Operator.axisVector i)
                  (T.erase (originLine i)))) x -
              Complex.exp (-Complex.I * p i) *
                inner ℂ (walshL2 (translateWalshIndex (Operator.axisVector i)
                  (T.erase (originLine i)))) x)
        else 0 := by
  rw [walshRaise, ContinuousLinearMap.sum_apply, inner_sum]
  exact Finset.sum_congr rfl fun i _ => inner_walshL2_walshRaiseDir p i T x

/-- Summing the two directions gives the full lowering coefficient. -/
theorem inner_walshL2_walshLower (p : Fin 2 -> Real)
    (T : Finset LineIndex) (x : WalshL2) :
    inner ℂ (walshL2 T) (walshLower p x) =
      ∑ i : Fin 2,
        if originLine i ∈ T then 0
        else
          -((2 : ℂ)⁻¹ *
            (Complex.exp (Complex.I * p i) *
                inner ℂ (walshL2 (translateWalshIndex (-Operator.axisVector i)
                  (insert (originLine i) T))) x -
              Complex.exp (-Complex.I * p i) *
                inner ℂ (walshL2 (translateWalshIndex (Operator.axisVector i)
                  (insert (originLine i) T))) x)) := by
  rw [walshLower, ContinuousLinearMap.sum_apply, inner_sum]
  exact Finset.sum_congr rfl fun i _ => inner_walshL2_walshLowerDir p i T x

/-! ### Degree bookkeeping and operator norms

`D` maps `H_n` into `H_{n+1}` and `D*` maps `H_n` into `H_{n-1}`
(`manuscript.tex:735-737`). -/

theorem originRaise_walshL2_mem_degree (i : Fin 2) {n : ℕ}
    (S : Finset LineIndex) (hS : S.card = n) :
    originRaise i (walshL2 S) ∈ walshDegree (n + 1) := by
  rw [originRaise_walshL2]
  by_cases h : originLine i ∈ S
  · rw [if_pos h]
    exact Submodule.zero_mem _
  · rw [if_neg h]
    have hcard : (insert (originLine i) S).card = n + 1 := by
      rw [Finset.card_insert_of_notMem h, hS]
    simpa [hcard] using walshL2_mem_degree (insert (originLine i) S)

theorem originLower_walshL2_mem_degree (i : Fin 2) {n : ℕ}
    (S : Finset LineIndex) (hS : S.card = n) :
    originLower i (walshL2 S) ∈ walshDegree (n - 1) := by
  rw [originLower_walshL2]
  by_cases h : originLine i ∈ S
  · rw [if_pos h]
    have hcard : (S.erase (originLine i)).card = n - 1 := by
      rw [Finset.card_erase_of_mem h, hS]
    simpa [hcard] using walshL2_mem_degree (S.erase (originLine i))
  · rw [if_neg h]
    exact Submodule.zero_mem _

theorem walshRaise_walshL2_mem_degree (p : Fin 2 -> Real) {n : ℕ}
    (S : Finset LineIndex) (hS : S.card = n) :
    walshRaise p (walshL2 S) ∈ walshDegree (n + 1) := by
  rw [walshRaise, ContinuousLinearMap.sum_apply]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [walshRaiseDir, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, fiberSkewTerm_walshL2, map_sub, map_smul,
    map_smul]
  refine Submodule.smul_mem _ _ (Submodule.sub_mem _
    (Submodule.smul_mem _ _ ?_) (Submodule.smul_mem _ _ ?_))
  · exact originRaise_walshL2_mem_degree i _
      ((card_translateWalshIndex _ S).trans hS)
  · exact originRaise_walshL2_mem_degree i _
      ((card_translateWalshIndex _ S).trans hS)

theorem walshLower_walshL2_mem_degree (p : Fin 2 -> Real) {n : ℕ}
    (S : Finset LineIndex) (hS : S.card = n) :
    walshLower p (walshL2 S) ∈ walshDegree (n - 1) := by
  rw [walshLower, ContinuousLinearMap.sum_apply]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [walshLowerDir, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    fiberSkewTerm_walshL2, map_sub, map_smul, map_smul]
  refine Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.sub_mem _
    (Submodule.smul_mem _ _ ?_) (Submodule.smul_mem _ _ ?_)))
  · exact originLower_walshL2_mem_degree i _
      ((card_translateWalshIndex _ S).trans hS)
  · exact originLower_walshL2_mem_degree i _
      ((card_translateWalshIndex _ S).trans hS)

private theorem walshDegree_le_comap {n m : ℕ} (T : WalshL2 →L[ℂ] WalshL2)
    (h : ∀ S : Finset LineIndex, S.card = n → T (walshL2 S) ∈ walshDegree m) :
    walshDegree n ≤ Submodule.comap (T : WalshL2 →ₗ[ℂ] WalshL2)
      (walshDegree m) := by
  refine Submodule.topologicalClosure_minimal _ ?_ ?_
  · rw [Submodule.span_le]
    rintro _ ⟨S, hS, rfl⟩
    exact h S hS
  · exact IsClosed.preimage T.continuous
      (Submodule.isClosed_topologicalClosure _)

/-- `D` maps the closed degree-`n` chaos into the degree-`(n+1)` chaos. -/
theorem walshRaise_mem_walshDegree (p : Fin 2 -> Real) {n : ℕ} {x : WalshL2}
    (hx : x ∈ walshDegree n) : walshRaise p x ∈ walshDegree (n + 1) :=
  walshDegree_le_comap (n := n) (m := n + 1) (walshRaise p)
    (fun S hS => walshRaise_walshL2_mem_degree p S hS) hx

/-- `D*` maps the closed degree-`n` chaos into the degree-`(n-1)` chaos. -/
theorem walshLower_mem_walshDegree (p : Fin 2 -> Real) {n : ℕ} {x : WalshL2}
    (hx : x ∈ walshDegree n) : walshLower p x ∈ walshDegree (n - 1) :=
  walshDegree_le_comap (n := n) (m := n - 1) (walshLower p)
    (fun S hS => walshLower_walshL2_mem_degree p S hS) hx

/-- The raising coefficient vanishes at every index set that avoids both origin
lines. -/
theorem inner_walshL2_walshRaise_eq_zero (p : Fin 2 -> Real)
    {T : Finset LineIndex} (hT : ∀ i : Fin 2, originLine i ∉ T) (x : WalshL2) :
    inner ℂ (walshL2 T) (walshRaise p x) = 0 := by
  rw [inner_walshL2_walshRaise]
  exact Finset.sum_eq_zero fun i _ => if_neg (hT i)

theorem originRaise_norm_le (i : Fin 2) : ‖originRaise i‖ ≤ 1 := by
  calc
    ‖originRaise i‖ ≤ ‖walshProjection (fun S => originLine i ∈ S)‖ *
        ‖originSignMultiplier i‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 := by
      refine mul_le_mul ?_ (originSignMultiplier_norm_le i) (norm_nonneg _)
        zero_le_one
      exact (walshSubspace (fun S => originLine i ∈ S)).starProjection_norm_le
    _ = 1 := by norm_num

theorem originLower_norm_le (i : Fin 2) : ‖originLower i‖ ≤ 1 := by
  calc
    ‖originLower i‖ ≤ ‖walshProjection (fun S => originLine i ∉ S)‖ *
        ‖originSignMultiplier i‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 := by
      refine mul_le_mul ?_ (originSignMultiplier_norm_le i) (norm_nonneg _)
        zero_le_one
      exact (walshSubspace (fun S => originLine i ∉ S)).starProjection_norm_le
    _ = 1 := by norm_num

theorem walshRaiseDir_norm_le (p : Fin 2 -> Real) (i : Fin 2) :
    ‖walshRaiseDir p i‖ ≤ 1 := by
  have hhalf : ‖(2 : ℂ)⁻¹‖ = (2 : ℝ)⁻¹ := by norm_num
  calc
    ‖walshRaiseDir p i‖ ≤ ‖(2 : ℂ)⁻¹‖ * ‖originRaise i ∘L fiberSkewTerm p i‖ :=
      ContinuousLinearMap.opNorm_smul_le _ _
    _ ≤ (2 : ℝ)⁻¹ * (1 * 2) := by
      rw [hhalf]
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul (originRaise_norm_le i) (fiberSkewTerm_norm_le p i)
          (norm_nonneg _) zero_le_one)
    _ = 1 := by norm_num

theorem walshRaise_norm_le (p : Fin 2 -> Real) : ‖walshRaise p‖ ≤ 2 := by
  calc
    ‖walshRaise p‖ ≤ ∑ i : Fin 2, ‖walshRaiseDir p i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 2, (1 : ℝ) := by
      gcongr with i
      exact walshRaiseDir_norm_le p i
    _ = 2 := by norm_num

theorem walshLowerDir_norm_le (p : Fin 2 -> Real) (i : Fin 2) :
    ‖walshLowerDir p i‖ ≤ 1 := by
  have hhalf : ‖(2 : ℂ)⁻¹‖ = (2 : ℝ)⁻¹ := by norm_num
  rw [walshLowerDir, norm_neg]
  calc
    ‖(2 : ℂ)⁻¹ • (originLower i ∘L fiberSkewTerm p i)‖ ≤
        ‖(2 : ℂ)⁻¹‖ * ‖originLower i ∘L fiberSkewTerm p i‖ :=
      ContinuousLinearMap.opNorm_smul_le _ _
    _ ≤ (2 : ℝ)⁻¹ * (1 * 2) := by
      rw [hhalf]
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul (originLower_norm_le i) (fiberSkewTerm_norm_le p i)
          (norm_nonneg _) zero_le_one)
    _ = 1 := by norm_num

theorem walshLower_norm_le (p : Fin 2 -> Real) : ‖walshLower p‖ ≤ 2 := by
  calc
    ‖walshLower p‖ ≤ ∑ i : Fin 2, ‖walshLowerDir p i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 2, (1 : ℝ) := by
      gcongr with i
      exact walshLowerDir_norm_le p i
    _ = 2 := by norm_num

end

end Manhattan.Glue
