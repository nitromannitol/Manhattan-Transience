import Manhattan.Walsh.Basic
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Finset-indexed Walsh coefficients and the raising/lowering split

The coefficient carrier is indexed directly by finite sets of line indices.
This is the factorial-free version of equations (17) and (18).

Paper: `manuscript.tex:719-740`.
-/

open MeasureTheory
open scoped BigOperators ComplexConjugate symmDiff

namespace Manhattan

noncomputable section

/-- Finitely supported coefficients of Walsh characters. -/
abbrev WalshCoefficient := Finset LineIndex →₀ ℂ

/-- A coefficient belongs to homogeneous degree `n` when every member of its
support is indexed by an `n`-element set of lines. -/
def IsWalshDegree (n : ℕ) (c : WalshCoefficient) : Prop :=
  ∀ S ∈ c.support, S.card = n

theorem isWalshDegree_zero (n : ℕ) : IsWalshDegree n 0 := by
  simp [IsWalshDegree]

theorem isWalshDegree_single {n : ℕ} {S : Finset LineIndex} {a : ℂ}
    (hS : S.card = n) :
    IsWalshDegree n (Finsupp.single S a) := by
  intro T hT
  have hTS : T = S := by
    by_contra hTS
    apply Finsupp.mem_support_iff.mp hT
    simp [Ne.symm hTS]
  simpa [hTS] using hS

theorem IsWalshDegree.add {n : ℕ} {c d : WalshCoefficient}
    (hc : IsWalshDegree n c) (hd : IsWalshDegree n d) :
    IsWalshDegree n (c + d) := by
  intro S hS
  have hne : c S + d S ≠ 0 := Finsupp.mem_support_iff.mp hS
  by_cases hcs : c S = 0
  · apply hd S
    exact Finsupp.mem_support_iff.mpr (by simpa [hcs] using hne)
  · apply hc S
    exact Finsupp.mem_support_iff.mpr hcs

theorem IsWalshDegree.neg {n : ℕ} {c : WalshCoefficient}
    (hc : IsWalshDegree n c) : IsWalshDegree n (-c) := by
  intro S hS
  apply hc S
  exact Finsupp.mem_support_iff.mpr (by
    simpa using Finsupp.mem_support_iff.mp hS)

theorem IsWalshDegree.sub {n : ℕ} {c d : WalshCoefficient}
    (hc : IsWalshDegree n c) (hd : IsWalshDegree n d) :
    IsWalshDegree n (c - d) := by
  simpa [sub_eq_add_neg] using hc.add hd.neg

theorem IsWalshDegree.smul {n : ℕ} {c : WalshCoefficient}
    (hc : IsWalshDegree n c) (a : ℂ) : IsWalshDegree n (a • c) := by
  intro S hS
  apply hc S
  exact Finsupp.mem_support_iff.mpr (by
    intro hzero
    apply Finsupp.mem_support_iff.mp hS
    simp [hzero])

theorem isWalshDegree_sum {I : Type*} {n : ℕ} (s : Finset I)
    (c : I → WalshCoefficient) (hc : ∀ i ∈ s, IsWalshDegree n (c i)) :
    IsWalshDegree n (∑ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [isWalshDegree_zero]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (hc i (Finset.mem_insert_self i s)).add
        (ih fun j hj => hc j (Finset.mem_insert_of_mem hj))

/-- The pointwise finite Walsh polynomial associated with a coefficient. -/
noncomputable def walshPolynomial (c : WalshCoefficient) (ω : Environment) : ℂ :=
  Finsupp.linearCombination ℂ (fun S => walshCharacter S ω) c

@[simp] theorem walshPolynomial_zero (ω : Environment) :
    walshPolynomial 0 ω = 0 := by
  simp [walshPolynomial]

@[simp] theorem walshPolynomial_add (c d : WalshCoefficient) (ω : Environment) :
    walshPolynomial (c + d) ω = walshPolynomial c ω + walshPolynomial d ω := by
  simp [walshPolynomial]

@[simp] theorem walshPolynomial_smul (a : ℂ) (c : WalshCoefficient) (ω : Environment) :
    walshPolynomial (a • c) ω = a * walshPolynomial c ω := by
  simp [walshPolynomial]

theorem walshPolynomial_finset_sum {I : Type*} (s : Finset I)
    (c : I → WalshCoefficient) (ω : Environment) :
    walshPolynomial (∑ i ∈ s, c i) ω = ∑ i ∈ s, walshPolynomial (c i) ω := by
  change (Finsupp.linearCombination ℂ (fun S => walshCharacter S ω))
      (∑ i ∈ s, c i) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rfl

@[simp] theorem walshPolynomial_ite (p : Prop) [Decidable p]
    (c d : WalshCoefficient) (ω : Environment) :
    walshPolynomial (if p then c else d) ω =
      if p then walshPolynomial c ω else walshPolynomial d ω := by
  by_cases hp : p <;> simp [hp]

theorem measurable_walshPolynomial (c : WalshCoefficient) :
    Measurable (walshPolynomial c) := by
  classical
  change Measurable fun ω => ∑ S ∈ c.support, c S * walshCharacter S ω
  exact Finset.measurable_fun_sum c.support fun S _ =>
    measurable_const.mul (measurable_walshCharacter S)

theorem memLp_walshPolynomial (c : WalshCoefficient) :
    MemLp (walshPolynomial c) 2 environmentLaw := by
  classical
  have hbound : ∀ ω, ‖walshPolynomial c ω‖ ≤ ∑ S ∈ c.support, ‖c S‖ := by
    intro ω
    change ‖∑ S ∈ c.support, c S * walshCharacter S ω‖ ≤ _
    refine (norm_sum_le _ _).trans ?_
    apply Finset.sum_le_sum
    intro S _
    simp
  exact MemLp.of_bound (measurable_walshPolynomial c).aestronglyMeasurable
    (∑ S ∈ c.support, ‖c S‖) (.of_forall hbound)

@[simp] theorem walshPolynomial_single (S : Finset LineIndex) (a : ℂ) (ω : Environment) :
    walshPolynomial (Finsupp.single S a) ω = a * walshCharacter S ω := by
  simp [walshPolynomial]

/-- Finite Walsh synthesis as mathlib's linear combination of the Walsh
orthonormal system. -/
noncomputable def walshSynthesis (c : WalshCoefficient) : WalshL2 :=
  Finsupp.linearCombination ℂ walshL2 c

/-- The `L²` synthesis has the advertised finite Walsh polynomial as a
representative. -/
theorem coeFn_walshSynthesis (c : WalshCoefficient) :
    (walshSynthesis c : Environment → ℂ) =ᵐ[environmentLaw] walshPolynomial c := by
  classical
  rw [walshSynthesis, Finsupp.linearCombination_apply]
  have hsum :
      (fun ω => (∑ S ∈ c.support, c S • walshL2 S : WalshL2) ω) =ᵐ[environmentLaw]
        fun ω => ∑ S ∈ c.support, c S * walshCharacter S ω := by
    induction c.support using Finset.induction with
    | empty => simp
    | @insert S s hS ih =>
        simp only [Finset.sum_insert hS]
        refine (Lp.coeFn_add _ _).trans ?_
        have hterm : (fun ω => (c S • walshL2 S : WalshL2) ω) =ᵐ[environmentLaw]
            fun ω => c S * walshCharacter S ω := by
          refine ((Lp.coeFn_smul (c S) (walshL2 S)).and (coeFn_walshL2 S)).mono ?_
          intro ω hω
          change (c S • walshL2 S : WalshL2) ω = c S * walshCharacter S ω
          rw [hω.1]
          change c S * (walshL2 S : Environment → ℂ) ω = c S * walshCharacter S ω
          rw [hω.2]
        exact hterm.add ih
  simpa only [walshPolynomial, Finsupp.linearCombination_apply, smul_eq_mul] using hsum

@[simp] theorem walshSynthesis_add (c d : WalshCoefficient) :
    walshSynthesis (c + d) = walshSynthesis c + walshSynthesis d := by
  exact map_add (Finsupp.linearCombination ℂ walshL2) c d

@[simp] theorem walshSynthesis_smul (a : ℂ) (c : WalshCoefficient) :
    walshSynthesis (a • c) = a • walshSynthesis c := by
  exact map_smul (Finsupp.linearCombination ℂ walshL2) a c

@[simp] theorem walshSynthesis_sub (c d : WalshCoefficient) :
    walshSynthesis (c - d) = walshSynthesis c - walshSynthesis d := by
  exact map_sub (Finsupp.linearCombination ℂ walshL2) c d

theorem walshSynthesis_sum {I : Type*} (s : Finset I)
    (c : I → WalshCoefficient) :
    walshSynthesis (∑ i ∈ s, c i) = ∑ i ∈ s, walshSynthesis (c i) := by
  exact map_sum (Finsupp.linearCombination ℂ walshL2) (fun i => c i) s

@[simp] theorem walshSynthesis_single (S : Finset LineIndex) (a : ℂ) :
    walshSynthesis (Finsupp.single S a) = a • walshL2 S := by
  exact Finsupp.linearCombination_single (R := ℂ) (v := walshL2) a S

/-- The coefficient inner product, with no factorial normalization. -/
noncomputable def walshCoefficientInner (c d : WalshCoefficient) : ℂ :=
  c.sum fun S a => conj a * d S

/-- Equation (17) in the Finset convention: finite Walsh synthesis
is an isometry and no `n!` occurs. -/
theorem inner_walshSynthesis (c d : WalshCoefficient) :
    inner ℂ (walshSynthesis c) (walshSynthesis d) = walshCoefficientInner c d := by
  exact orthonormal_walshL2.inner_finsupp_eq_sum_left c d

/-- The part of coordinate multiplication that raises the Walsh degree. -/
noncomputable def raiseCoefficient (l : LineIndex) (c : WalshCoefficient) : WalshCoefficient :=
  c.sum fun S a => if l ∈ S then 0 else Finsupp.single (insert l S) a

/-- The part of coordinate multiplication that lowers the Walsh degree. -/
noncomputable def lowerCoefficient (l : LineIndex) (c : WalshCoefficient) : WalshCoefficient :=
  c.sum fun S a => if l ∈ S then Finsupp.single (S.erase l) a else 0

@[simp] theorem raiseCoefficient_single (l : LineIndex) (S : Finset LineIndex) (a : ℂ) :
    raiseCoefficient l (Finsupp.single S a) =
      if l ∈ S then 0 else Finsupp.single (insert l S) a := by
  simp [raiseCoefficient]

@[simp] theorem lowerCoefficient_single (l : LineIndex) (S : Finset LineIndex) (a : ℂ) :
    lowerCoefficient l (Finsupp.single S a) =
      if l ∈ S then Finsupp.single (S.erase l) a else 0 := by
  simp [lowerCoefficient]

/-- Raising a singleton of degree `n` has degree `n+1`. -/
theorem isWalshDegree_raiseCoefficient_single {n : ℕ}
    (l : LineIndex) (S : Finset LineIndex) (a : ℂ) (hS : S.card = n) :
    IsWalshDegree (n + 1) (raiseCoefficient l (Finsupp.single S a)) := by
  rw [raiseCoefficient_single]
  by_cases hl : l ∈ S
  · simp [hl, isWalshDegree_zero]
  · simp only [hl, if_false]
    apply isWalshDegree_single
    simp [Finset.card_insert_of_notMem hl, hS]

/-- Lowering a singleton of positive degree `n` has degree `n-1`. -/
theorem isWalshDegree_lowerCoefficient_single {n : ℕ}
    (l : LineIndex) (S : Finset LineIndex) (a : ℂ) (hS : S.card = n) :
    IsWalshDegree (n - 1) (lowerCoefficient l (Finsupp.single S a)) := by
  rw [lowerCoefficient_single]
  by_cases hl : l ∈ S
  · simp only [hl, if_true]
    apply isWalshDegree_single
    have herase := Finset.card_erase_of_mem hl
    omega
  · simp [hl, isWalshDegree_zero]

/-- Multiplication by one coordinate sign removes that line when present and
inserts it when absent: the basis-level raising/lowering split of (18). -/
theorem coordinate_mul_walshCharacter (l : LineIndex) (S : Finset LineIndex)
    (ω : Environment) :
    coordinateCharacter l ω * walshCharacter S ω =
      if l ∈ S then walshCharacter (S.erase l) ω else walshCharacter (insert l S) ω := by
  classical
  by_cases hl : l ∈ S
  · have hdiff : ({l} : Finset LineIndex) ∆ S = S.erase l := by
      ext x
      simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_erase]
      by_cases hxl : x = l <;> simp_all
    rw [if_pos hl, ← hdiff, ← walshCharacter_mul]
    simp [walshCharacter]
  · have hdiff : ({l} : Finset LineIndex) ∆ S = insert l S := by
      ext x
      simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_insert]
      by_cases hxl : x = l <;> simp_all
    rw [if_neg hl, ← hdiff, ← walshCharacter_mul]
    simp [walshCharacter]

/-- The raising/lowering split on a single Walsh monomial. Linearity then
gives the split on every finite Walsh polynomial. -/
theorem coordinate_mul_single_walshPolynomial (l : LineIndex) (S : Finset LineIndex)
    (a : ℂ) (ω : Environment) :
    coordinateCharacter l ω * walshPolynomial (Finsupp.single S a) ω =
      walshPolynomial
        (raiseCoefficient l (Finsupp.single S a) +
          lowerCoefficient l (Finsupp.single S a)) ω := by
  by_cases hl : l ∈ S
  · rw [raiseCoefficient_single, lowerCoefficient_single, if_pos hl,
      if_pos hl, zero_add, walshPolynomial_single]
    rw [mul_left_comm, coordinate_mul_walshCharacter l S ω, if_pos hl]
    exact (walshPolynomial_single (S.erase l) a ω).symm
  · rw [raiseCoefficient_single, lowerCoefficient_single, if_neg hl,
      if_neg hl, add_zero, walshPolynomial_single]
    rw [mul_left_comm, coordinate_mul_walshCharacter l S ω, if_neg hl]
    exact (walshPolynomial_single (insert l S) a ω).symm

/-- Equation (18) for an arbitrary finite Walsh polynomial: coordinate
multiplication is the sum of its degree-raising and degree-lowering parts. -/
theorem coordinate_mul_walshPolynomial (l : LineIndex) (c : WalshCoefficient)
    (ω : Environment) :
    coordinateCharacter l ω * walshPolynomial c ω =
      walshPolynomial (raiseCoefficient l c + lowerCoefficient l c) ω := by
  classical
  change coordinateCharacter l ω *
      (∑ S ∈ c.support, c S * walshCharacter S ω) = _
  rw [raiseCoefficient, lowerCoefficient, walshPolynomial_add]
  change coordinateCharacter l ω *
      (∑ S ∈ c.support, c S * walshCharacter S ω) =
    walshPolynomial
        (∑ S ∈ c.support,
          if l ∈ S then 0 else Finsupp.single (insert l S) (c S)) ω +
      walshPolynomial
        (∑ S ∈ c.support,
          if l ∈ S then Finsupp.single (S.erase l) (c S) else 0) ω
  rw [walshPolynomial_finset_sum, walshPolynomial_finset_sum, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hl : l ∈ S
  · simp only [hl, if_pos, walshPolynomial_zero, walshPolynomial_single,
      zero_add]
    rw [mul_left_comm, coordinate_mul_walshCharacter l S ω, if_pos hl]
  · rw [if_neg hl, if_neg hl, walshPolynomial_single,
      walshPolynomial_zero, add_zero]
    rw [mul_left_comm, coordinate_mul_walshCharacter l S ω, if_neg hl]

end

end Manhattan
