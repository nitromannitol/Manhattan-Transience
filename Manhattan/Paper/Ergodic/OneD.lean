/-
The one dimensional return count.

Among the `2 ^ (2m)` sign words of length `2m`, exactly `C(2m, m)` sum to zero:
a word sums to zero exactly when half its entries are `+1`, and choosing which
half is choosing an `m`-element subset.
-/
import Manhattan.Paper.Ergodic.Factorize

namespace Manhattan.Paper.Ergodic

open Finset

/-- A sign word sums to zero exactly when exactly half its entries are `+1`. -/
theorem sum_sgnVal_eq_zero_iff (m : ℕ) (u : Fin (2 * m) → Bool) :
    (∑ i, sgnVal (u i) = 0) ↔ (univ.filter (fun i => u i = true)).card = m := by
  classical
  have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
    (s := (univ : Finset (Fin (2 * m)))) (p := fun i => u i = true)
  rw [Finset.card_fin] at hsplit
  have hsum : ∑ i, sgnVal (u i)
      = ((univ.filter (fun i => u i = true)).card : ℤ)
        - ((univ.filter (fun i => ¬ (u i = true))).card : ℤ) := by
    rw [← Finset.sum_filter_add_sum_filter_not univ (fun i => u i = true) (fun i => sgnVal (u i))]
    have h1 : ∑ i ∈ univ.filter (fun i => u i = true), sgnVal (u i)
        = ((univ.filter (fun i => u i = true)).card : ℤ) := by
      calc ∑ i ∈ univ.filter (fun i => u i = true), sgnVal (u i)
          = ∑ _i ∈ univ.filter (fun i => u i = true), (1 : ℤ) := by
            refine Finset.sum_congr rfl fun i hi => ?_
            have h : u i = true := (Finset.mem_filter.mp hi).2
            simp [sgnVal, h]
        _ = ((univ.filter (fun i => u i = true)).card : ℤ) := by simp
    have h2 : ∑ i ∈ univ.filter (fun i => ¬ (u i = true)), sgnVal (u i)
        = - ((univ.filter (fun i => ¬ (u i = true))).card : ℤ) := by
      calc ∑ i ∈ univ.filter (fun i => ¬ (u i = true)), sgnVal (u i)
          = ∑ _i ∈ univ.filter (fun i => ¬ (u i = true)), (-1 : ℤ) := by
            refine Finset.sum_congr rfl fun i hi => ?_
            have h : u i = false := by
              have hne := (Finset.mem_filter.mp hi).2
              cases hb : u i with
              | false => rfl
              | true => exact absurd hb hne
            simp [sgnVal, h]
        _ = - ((univ.filter (fun i => ¬ (u i = true))).card : ℤ) := by simp
    rw [h1, h2]; ring
  rw [hsum]
  omega

/-- **The one dimensional return count.** -/
theorem oneDCount_two_mul (m : ℕ) : oneDCount (2 * m) = Nat.centralBinom m := by
  classical
  have hpc : ((univ : Finset (Fin (2 * m))).powersetCard m).card = (2 * m).choose m := by
    rw [Finset.card_powersetCard, Finset.card_fin]
  rw [oneDCount, Nat.centralBinom_eq_two_mul_choose, ← hpc]
  refine Finset.card_bij (fun u _ => univ.filter (fun k => u k = true)) ?_ ?_ ?_
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,
      (sum_sgnVal_eq_zero_iff m u).mp hu⟩
  · intro a _ b _ hab
    funext k
    have : (k ∈ univ.filter (fun i => a i = true)) ↔ (k ∈ univ.filter (fun i => b i = true)) :=
      Finset.ext_iff.mp hab k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
    cases ha : a k <;> cases hb : b k <;> simp [ha, hb] at this ⊢
  · intro s hs
    refine ⟨fun k => decide (k ∈ s), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine (sum_sgnVal_eq_zero_iff m _).mpr ?_
      have hcard := (Finset.mem_powersetCard.mp hs).2
      have : univ.filter (fun k => (decide (k ∈ s)) = true) = s := by
        ext k; simp
      rw [this]; exact hcard
    · ext k; simp

end Manhattan.Paper.Ergodic
