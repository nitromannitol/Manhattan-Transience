/-
The planar return count is a square.

Rotating by 45 degrees turns a word of `n` lattice steps into a PAIR of
independent sign words, and the walk returns to the origin exactly when both
sign words do.  Counting is then multiplicative.
-/
import Manhattan.Paper.Ergodic.Rotation

namespace Manhattan.Paper.Ergodic

open Finset

/-- A word of steps is exactly a pair of sign words. -/
def wordEquiv (n : ℕ) : (Fin n → Step) ≃ (Fin n → Bool) × (Fin n → Bool) where
  toFun e := (fun k => (e k).sgn.1, fun k => (e k).sgn.2)
  invFun p := fun k => Step.ofSgn (p.1 k, p.2 k)
  left_inv e := by funext k; cases h : e k <;> simp [Step.ofSgn, Step.sgn, h]
  right_inv p := by
    apply Prod.ext <;> funext k <;>
      cases h1 : p.1 k <;> cases h2 : p.2 k <;>
        simp [Step.ofSgn, Step.sgn, h1, h2]

@[simp] theorem wordEquiv_fst (n : ℕ) (e : Fin n → Step) (k : Fin n) :
    (wordEquiv n e).1 k = (e k).sgn.1 := rfl

@[simp] theorem wordEquiv_snd (n : ℕ) (e : Fin n → Step) (k : Fin n) :
    (wordEquiv n e).2 k = (e k).sgn.2 := rfl

/-- The walk returns to the origin exactly when both rotated coordinates do. -/
theorem sum_vec_eq_zero_iff (n : ℕ) (e : Fin n → Step) :
    (∑ k, (e k).vec) = 0 ↔
      (∑ k, sgnVal ((wordEquiv n e).1 k) = 0) ∧ (∑ k, sgnVal ((wordEquiv n e).2 k) = 0) := by
  have hfst : (∑ k, (e k).vec).1 = ∑ k, ((e k).vec).1 := Prod.fst_sum
  have hsnd : (∑ k, (e k).vec).2 = ∑ k, ((e k).vec).2 := Prod.snd_sum
  have hsum1 : ∑ k, sgnVal ((wordEquiv n e).1 k)
      = (∑ k, ((e k).vec).1) + (∑ k, ((e k).vec).2) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => ((rot_vec (e k)).1).symm
  have hsum2 : ∑ k, sgnVal ((wordEquiv n e).2 k)
      = (∑ k, ((e k).vec).1) - (∑ k, ((e k).vec).2) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => ((rot_vec (e k)).2).symm
  rw [hsum1, hsum2]
  constructor
  · intro h
    have h' : ((∑ k, ((e k).vec).1), (∑ k, ((e k).vec).2)) = ((0 : ℤ), (0 : ℤ)) := by
      rw [← hfst, ← hsnd]; rw [h]; rfl
    exact (eq_zero_iff_rot _ _).mp h'
  · intro h
    have h' := (eq_zero_iff_rot (∑ k, ((e k).vec).1) (∑ k, ((e k).vec).2)).mpr h
    have : (∑ k, (e k).vec) = ((0 : ℤ), (0 : ℤ)) := by
      rw [Prod.ext_iff]; rw [hfst, hsnd]
      exact ⟨congrArg Prod.fst h', congrArg Prod.snd h'⟩
    simpa using this

/-- The one dimensional return count at length `n`. -/
def oneDCount (n : ℕ) : ℕ :=
  (univ.filter (fun u : Fin n → Bool => ∑ k, sgnVal (u k) = 0)).card

/-- **The planar count is a square.** -/
theorem srwCount_eq_sq (n : ℕ) : srwCount n 0 = (oneDCount n) ^ 2 := by
  have hcard : srwCount n 0
      = (univ.filter (fun e : Fin n → Step => (∑ k, (e k).vec) = 0)).card := by
    rw [srwCount, Finset.card_filter]
    exact Finset.sum_congr rfl fun e _ => by simp
  rw [hcard]
  have hfilter : (univ.filter (fun e : Fin n → Step => (∑ k, (e k).vec) = 0)).card
      = (univ.filter (fun p : (Fin n → Bool) × (Fin n → Bool) =>
            (∑ k, sgnVal (p.1 k) = 0) ∧ (∑ k, sgnVal (p.2 k) = 0))).card := by
    apply Finset.card_bij (fun e _ => wordEquiv n e)
    · intro e he
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
      exact (sum_vec_eq_zero_iff n e).mp he
    · intro a _ b _ hab
      exact (wordEquiv n).injective hab
    · intro p hp
      refine ⟨(wordEquiv n).symm p, ?_, by simp⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      have := (sum_vec_eq_zero_iff n ((wordEquiv n).symm p)).mpr
      simpa using this (by simpa using hp)
  have hprod : (univ.filter (fun p : (Fin n → Bool) × (Fin n → Bool) =>
        (∑ k, sgnVal (p.1 k) = 0) ∧ (∑ k, sgnVal (p.2 k) = 0)))
      = (univ.filter (fun u : Fin n → Bool => ∑ k, sgnVal (u k) = 0)) ×ˢ
        (univ.filter (fun u : Fin n → Bool => ∑ k, sgnVal (u k) = 0)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
  rw [hfilter, hprod, Finset.card_product, oneDCount, sq]

end Manhattan.Paper.Ergodic
