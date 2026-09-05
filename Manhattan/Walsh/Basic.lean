import Manhattan.Model.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Walsh characters of the fair-coin environment

Paper: `manuscript.tex:701-741`. The formalization replaces symmetric tuple
coefficients by finite sets of distinct line indices.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ComplexConjugate ENNReal NNReal symmDiff

namespace Manhattan

noncomputable section

/-- The complex-valued character of one fair sign. -/
def orientationCharacter (o : Orientation) : ℂ := o.sign

@[simp] theorem orientationCharacter_negative :
    orientationCharacter .negative = -1 := by
  norm_num [orientationCharacter, Orientation.sign]

@[simp] theorem orientationCharacter_positive :
    orientationCharacter .positive = 1 := by
  norm_num [orientationCharacter, Orientation.sign]

@[simp] theorem orientationCharacter_sq (o : Orientation) :
    orientationCharacter o * orientationCharacter o = 1 := by
  cases o <;> norm_num [orientationCharacter, Orientation.sign]

@[simp] theorem norm_orientationCharacter (o : Orientation) :
    ‖orientationCharacter o‖ = 1 := by
  cases o <;> norm_num [orientationCharacter, Orientation.sign]

@[simp] theorem star_orientationCharacter (o : Orientation) :
    starRingEnd ℂ (orientationCharacter o) = orientationCharacter o := by
  cases o <;> simp

/-- The coordinate sign attached to a line. -/
def coordinateCharacter (l : LineIndex) (ω : Environment) : ℂ :=
  orientationCharacter (ω l)

@[simp] theorem norm_coordinateCharacter (l : LineIndex) (ω : Environment) :
    ‖coordinateCharacter l ω‖ = 1 := norm_orientationCharacter (ω l)

@[simp] theorem coordinateCharacter_sq (l : LineIndex) (ω : Environment) :
    coordinateCharacter l ω * coordinateCharacter l ω = 1 :=
  orientationCharacter_sq (ω l)

@[simp] theorem star_coordinateCharacter (l : LineIndex) (ω : Environment) :
    starRingEnd ℂ (coordinateCharacter l ω) = coordinateCharacter l ω :=
  star_orientationCharacter (ω l)

theorem measurable_coordinateCharacter (l : LineIndex) :
    Measurable (coordinateCharacter l) := by
  exact (measurable_of_finite orientationCharacter).comp (measurable_pi_apply l)

/-- The Walsh character indexed by a finite set of distinct lines. -/
def walshCharacter (S : Finset LineIndex) (ω : Environment) : ℂ :=
  ∏ l ∈ S, coordinateCharacter l ω

theorem measurable_walshCharacter (S : Finset LineIndex) :
    Measurable (walshCharacter S) := by
  exact S.measurable_fun_prod fun l _ => measurable_coordinateCharacter l

@[simp] theorem star_walshCharacter (S : Finset LineIndex) (ω : Environment) :
    starRingEnd ℂ (walshCharacter S ω) = walshCharacter S ω := by
  simp [walshCharacter]

@[simp] theorem norm_walshCharacter (S : Finset LineIndex) (ω : Environment) :
    ‖walshCharacter S ω‖ = 1 := by
  simp [walshCharacter]

theorem memLp_walshCharacter (S : Finset LineIndex) :
    MemLp (walshCharacter S) 2 environmentLaw := by
  exact MemLp.of_bound (measurable_walshCharacter S).aestronglyMeasurable 1
    (.of_forall fun ω => by simp)

/-- The complex Hilbert space `L²(P)` of the environment. -/
abbrev WalshL2 := Environment →₂[environmentLaw] ℂ

/-- A Walsh character as an element of `L²(P)`. -/
noncomputable def walshL2 (S : Finset LineIndex) : WalshL2 :=
  (memLp_walshCharacter S).toLp (walshCharacter S)

theorem coeFn_walshL2 (S : Finset LineIndex) :
    (walshL2 S : Environment → ℂ) =ᵐ[environmentLaw] walshCharacter S :=
  MemLp.coeFn_toLp (memLp_walshCharacter S)

/-- A single fair sign has mean zero. -/
theorem integral_coordinateCharacter (l : LineIndex) :
    ∫ ω, coordinateCharacter l ω ∂environmentLaw = 0 := by
  calc
    ∫ ω, coordinateCharacter l ω ∂environmentLaw =
        ∫ o, orientationCharacter o ∂(environmentLaw.map fun ω => ω l) := by
          exact (integral_map (measurable_pi_apply l).aemeasurable
            (measurable_of_finite orientationCharacter).aestronglyMeasurable).symm
    _ = ∫ o, orientationCharacter o ∂fairCoin := by
      rw [(measurePreserving_orientation l).map_eq]
    _ = 0 := by
      rw [fairCoin, PMF.integral_eq_sum]
      rw [show Finset.univ = {.negative, .positive} by decide]
      have hcard : Fintype.card Orientation = 2 := by decide
      rw [Finset.sum_insert
        (by decide : Orientation.negative ∉ ({Orientation.positive} : Finset Orientation)),
        Finset.sum_singleton]
      norm_num [fairCoinPMF, orientationCharacter, Orientation.sign, hcard]

/-- A nonconstant Walsh character has mean zero. -/
theorem integral_walshCharacter_eq_zero {S : Finset LineIndex} (hS : S.Nonempty) :
    ∫ ω, walshCharacter S ω ∂environmentLaw = 0 := by
  let X : S → Environment → ℂ := fun l ω => coordinateCharacter l ω
  have hX : iIndepFun X environmentLaw := by
    exact iIndepFun_orientation.precomp Subtype.val_injective |>.comp
      (fun _ => orientationCharacter) (fun _ => measurable_of_finite orientationCharacter)
  have hprod := hX.integral_fun_prod_eq_prod_integral
    (fun l => (measurable_coordinateCharacter l).aestronglyMeasurable)
  rw [show walshCharacter S = fun ω => ∏ l : S, X l ω by
    funext ω
    change (∏ l ∈ S, coordinateCharacter l ω) = ∏ l : S, coordinateCharacter l ω
    exact (Finset.prod_coe_sort S (fun l => coordinateCharacter l ω)).symm]
  rw [hprod]
  obtain ⟨l, hl⟩ := hS
  rw [Finset.prod_eq_zero (Finset.mem_univ ⟨l, hl⟩)]
  exact integral_coordinateCharacter l

@[simp] theorem integral_walshCharacter_empty :
    ∫ ω, walshCharacter ∅ ω ∂environmentLaw = 1 := by
  simp [walshCharacter]

/-- Multiplying two characters toggles precisely their symmetric difference. -/
theorem walshCharacter_mul (S T : Finset LineIndex) (ω : Environment) :
    walshCharacter S ω * walshCharacter T ω = walshCharacter (S ∆ T) ω := by
  classical
  induction S using Finset.induction_on generalizing T with
  | empty =>
      have hdiff : (∅ : Finset LineIndex) ∆ T = T := by
        ext x
        simp only [Finset.mem_symmDiff, Finset.notMem_empty]
        tauto
      rw [hdiff]
      simp [walshCharacter]
  | @insert l S hl ih =>
      have hinsert : walshCharacter (insert l S) ω =
          coordinateCharacter l ω * walshCharacter S ω := by
        rw [walshCharacter, Finset.prod_insert hl]
        rfl
      by_cases hlt : l ∈ T
      · have hdiff : insert l S ∆ T = S ∆ T.erase l := by
          ext x
          simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_erase]
          by_cases hxl : x = l <;> simp_all
        have hT : walshCharacter T ω =
            coordinateCharacter l ω * walshCharacter (T.erase l) ω := by
          calc
            walshCharacter T ω = walshCharacter (insert l (T.erase l)) ω := by
              rw [Finset.insert_erase hlt]
            _ = coordinateCharacter l ω * walshCharacter (T.erase l) ω := by
              rw [walshCharacter, Finset.prod_insert (Finset.notMem_erase l T)]
              rfl
        rw [hdiff, hinsert, hT]
        calc
          (coordinateCharacter l ω * walshCharacter S ω) *
                (coordinateCharacter l ω * walshCharacter (T.erase l) ω) =
              (coordinateCharacter l ω * coordinateCharacter l ω) *
                (walshCharacter S ω * walshCharacter (T.erase l) ω) := by ring
          _ = walshCharacter S ω * walshCharacter (T.erase l) ω := by simp
          _ = walshCharacter (S ∆ T.erase l) ω := ih (T.erase l)
      · have hdiff : insert l S ∆ T = insert l (S ∆ T) := by
          ext x
          simp only [Finset.mem_symmDiff, Finset.mem_insert]
          by_cases hxl : x = l <;> simp_all
        have hnot : l ∉ S ∆ T := by
          simp only [Finset.mem_symmDiff]
          simp [hl, hlt]
        have hright : walshCharacter (insert l (S ∆ T)) ω =
            coordinateCharacter l ω * walshCharacter (S ∆ T) ω := by
          rw [walshCharacter, Finset.prod_insert hnot]
          rfl
        rw [hdiff, hinsert, hright]
        rw [mul_assoc, ih T]

/-- Orthonormality of the Walsh characters in `L²(P)`. -/
theorem inner_walshL2 (S T : Finset LineIndex) :
    inner ℂ (walshL2 S) (walshL2 T) = if S = T then 1 else 0 := by
  rw [L2.inner_def]
  have hST : (fun ω => inner ℂ (walshL2 S ω) (walshL2 T ω)) =ᵐ[environmentLaw]
      fun ω => walshCharacter (S ∆ T) ω := by
    filter_upwards [coeFn_walshL2 S, coeFn_walshL2 T] with ω hS hT
    rw [hS, hT]
    simp only [RCLike.inner_apply, star_walshCharacter]
    rw [mul_comm]
    exact walshCharacter_mul S T ω
  rw [integral_congr_ae hST]
  by_cases h : S = T
  · subst T
    simp [walshCharacter]
  · have hne : (S ∆ T).Nonempty := Finset.symmDiff_nonempty.mpr h
    rw [integral_walshCharacter_eq_zero hne, if_neg h]

/-- The Walsh family is an orthonormal system. -/
theorem orthonormal_walshL2 : Orthonormal ℂ walshL2 := by
  rw [orthonormal_iff_ite]
  exact inner_walshL2

/-- The closed homogeneous Walsh subspace of degree `n`. -/
noncomputable def walshDegree (n : ℕ) : Submodule ℂ WalshL2 :=
  Submodule.topologicalClosure
    (Submodule.span ℂ {f | ∃ S : Finset LineIndex, S.card = n ∧ f = walshL2 S})

theorem walshL2_mem_degree (S : Finset LineIndex) : walshL2 S ∈ walshDegree S.card := by
  apply Submodule.le_topologicalClosure
  apply Submodule.subset_span
  exact ⟨S, rfl, rfl⟩

end

end Manhattan
