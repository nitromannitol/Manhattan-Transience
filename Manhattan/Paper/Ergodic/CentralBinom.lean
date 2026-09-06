/-
A sharp lower bound on the central binomial coefficient.

Mathlib has `Nat.four_pow_le_two_mul_self_mul_centralBinom`, `4 ^ n ≤ 2 * n *
centralBinom n`.  That is a factor of `√n` weaker than what recurrence of the
two dimensional walk needs: it gives `centralBinom n ^ 2 / 16 ^ n ≳ 1 / n ^ 2`,
a convergent series, where the truth is `≳ 1 / n`, a divergent one.

The sharp form below is proved by induction with exactly one unit of slack at
each step, which is why the weaker bound cannot be pushed to give it.  Written
Verified here.
-/
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Positivity

namespace Manhattan.Paper.Ergodic


theorem sixteen_pow_le (n : ℕ) (hn : 1 ≤ n) :
    16 ^ n ≤ 4 * n * (Nat.centralBinom n) ^ 2 := by
  induction n with
  | zero => exact absurd hn (Nat.not_succ_le_zero 0)
  | succ m ih =>
    cases m with
    | zero =>
      norm_num [Nat.centralBinom, Nat.choose]
    | succ k =>
      have squareStep : (k + 2) ^ 2 * (Nat.centralBinom (k + 2)) ^ 2
          = 4 * (2 * k + 3) ^ 2 * (Nat.centralBinom (k + 1)) ^ 2 := by
        have h := Nat.succ_mul_centralBinom_succ (k + 1)
        have hsq : ((k + 2) * Nat.centralBinom (k + 2)) ^ 2
            = (2 * (2 * k + 3) * Nat.centralBinom (k + 1)) ^ 2 := by
          rw [show k + 2 = k + 1 + 1 from rfl, h]
          ring_nf
        calc (k + 2) ^ 2 * (Nat.centralBinom (k + 2)) ^ 2
            = ((k + 2) * Nat.centralBinom (k + 2)) ^ 2 := by ring
          _ = (2 * (2 * k + 3) * Nat.centralBinom (k + 1)) ^ 2 := hsq
          _ = 4 * (2 * k + 3) ^ 2 * (Nat.centralBinom (k + 1)) ^ 2 := by ring
      have squareArith : 4 * (k + 1) * (k + 2) ≤ (2 * k + 3) ^ 2 := by
        have hExpand : (2 * k + 3) ^ 2 = 4 * (k + 1) * (k + 1) + 4 * (k + 1) + 1 := by ring
        calc 4 * (k + 1) * (k + 2)
            = 4 * (k + 1) * (k + 1) + 4 * (k + 1) := by ring
          _ ≤ 4 * (k + 1) * (k + 1) + 4 * (k + 1) + 1 := by omega
          _ = (2 * k + 3) ^ 2 := hExpand.symm
      have hIH := ih k.succ_pos
      have lowerBound : 16 ^ (k + 1) * (k + 2)
          ≤ (2 * k + 3) ^ 2 * (Nat.centralBinom (k + 1)) ^ 2 := by
        calc 16 ^ (k + 1) * (k + 2)
            ≤ 4 * (k + 1) * (Nat.centralBinom (k + 1)) ^ 2 * (k + 2) :=
              Nat.mul_le_mul_right (k + 2) hIH
          _ = 4 * (k + 1) * (k + 2) * (Nat.centralBinom (k + 1)) ^ 2 := by ring
          _ ≤ (2 * k + 3) ^ 2 * (Nat.centralBinom (k + 1)) ^ 2 :=
            Nat.mul_le_mul_right ((Nat.centralBinom (k + 1)) ^ 2) squareArith
      have scaled : 16 ^ (k + 1) * 16 * (k + 2)
          ≤ 4 * (k + 2) ^ 2 * (Nat.centralBinom (k + 2)) ^ 2 := by
        calc 16 ^ (k + 1) * 16 * (k + 2)
            = 16 * (16 ^ (k + 1) * (k + 2)) := by ring
          _ ≤ 16 * ((2 * k + 3) ^ 2 * (Nat.centralBinom (k + 1)) ^ 2) :=
            Nat.mul_le_mul_left 16 lowerBound
          _ = 16 * (2 * k + 3) ^ 2 * (Nat.centralBinom (k + 1)) ^ 2 := by ring
          _ = 4 * (k + 2) ^ 2 * (Nat.centralBinom (k + 2)) ^ 2 := by
            rw [show (4:ℕ) * (k + 2) ^ 2 * (Nat.centralBinom (k + 2)) ^ 2
                  = 4 * ((k + 2) ^ 2 * (Nat.centralBinom (k + 2)) ^ 2) from by ring,
                squareStep]
            ring
      have multiplied : (k + 2) * 16 ^ (k + 2)
          ≤ (k + 2) * (4 * (k + 2) * (Nat.centralBinom (k + 2)) ^ 2) := by
        calc (k + 2) * 16 ^ (k + 2)
            = (k + 2) * (16 ^ (k + 1) * 16) := by ring
          _ = 16 ^ (k + 1) * 16 * (k + 2) := by ring
          _ ≤ 4 * (k + 2) ^ 2 * (Nat.centralBinom (k + 2)) ^ 2 := scaled
          _ = (k + 2) * (4 * (k + 2) * (Nat.centralBinom (k + 2)) ^ 2) := by ring
      exact Nat.le_of_mul_le_mul_left multiplied (by omega : 0 < k + 2)

theorem one_div_le_centralBinom_sq_div (n : ℕ) (hn : 1 ≤ n) :
    (1 : ℝ) / (4 * n) ≤ ((Nat.centralBinom n : ℝ)) ^ 2 / 16 ^ n := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  rw [one_mul, mul_comm]
  exact_mod_cast sixteen_pow_le n hn


end Manhattan.Paper.Ergodic
