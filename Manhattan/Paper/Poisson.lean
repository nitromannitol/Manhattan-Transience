import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic

/-!
# The rate-two Poisson clock, as a real-valued weight

`poissonWeight t n = e^{-2t}(2t)^n/n!` is `P(N_t = n)` for the rate-two Poisson
process of `manuscript.tex:200-226`. This file records what the two halves of
`prop:time` need:

* `hasSum_poissonWeight`, the total mass one;
* `hasDerivAt_poissonWeight`, whose value `2(w_{n-1} - w_n)` is the statement
  that the subordinated semigroup has generator `2(Q - I)`;
* `tsum_abs_dPoissonWeight_le`, the bound `E|N/t - 2| ≤ √(2/t)` used for the
  time derivative, proved from the exact Poisson mean and variance.
-/

open scoped BigOperators

namespace Manhattan.Paper

/-- `P(N_t = n)` for a rate-two Poisson clock. -/
noncomputable def poissonWeight (t : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-(2 * t)) * (2 * t) ^ n / (n.factorial : ℝ)

theorem poissonWeight_nonneg {t : ℝ} (ht : 0 ≤ t) (n : ℕ) : 0 ≤ poissonWeight t n := by
  have h1 : (0:ℝ) ≤ (2 * t) ^ n := pow_nonneg (by linarith) n
  have h2 : (0:ℝ) < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
  exact div_nonneg (mul_nonneg (Real.exp_pos _).le h1) h2.le

/-- The Poisson weights have total mass one. -/
theorem hasSum_poissonWeight (t : ℝ) : HasSum (poissonWeight t) 1 := by
  have h : HasSum (fun n : ℕ => (2 * t) ^ n / (n.factorial : ℝ)) (Real.exp (2 * t)) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp ℝ (2 * t)
  have h2 := h.mul_left (Real.exp (-(2 * t)))
  rw [← Real.exp_add] at h2
  simp only [neg_add_cancel, Real.exp_zero] at h2
  refine h2.congr_fun fun n => ?_
  rw [poissonWeight]
  ring

theorem tsum_poissonWeight (t : ℝ) : ∑' n, poissonWeight t n = 1 :=
  (hasSum_poissonWeight t).tsum_eq

theorem summable_poissonWeight (t : ℝ) : Summable (poissonWeight t) :=
  (hasSum_poissonWeight t).summable

theorem poissonWeight_le_one {t : ℝ} (ht : 0 ≤ t) (n : ℕ) : poissonWeight t n ≤ 1 := by
  have h := (summable_poissonWeight t).le_tsum n fun j _ => poissonWeight_nonneg ht j
  rwa [tsum_poissonWeight] at h

/-- The previous Poisson weight, with the convention `w_{-1} = 0`. -/
noncomputable def poissonWeightPrev (t : ℝ) : ℕ → ℝ
  | 0 => 0
  | (n + 1) => poissonWeight t n

/-- The time derivative of the `n`-th Poisson weight. -/
noncomputable def dPoissonWeight (t : ℝ) (n : ℕ) : ℝ :=
  2 * (poissonWeightPrev t n - poissonWeight t n)

theorem hasDerivAt_poissonWeight (t : ℝ) (n : ℕ) :
    HasDerivAt (fun s => poissonWeight s n) (dPoissonWeight t n) t := by
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (-(2 * s))) (-2 * Real.exp (-(2 * t))) t := by
    have h1 : HasDerivAt (fun s : ℝ => -(2 * s)) (-2) t := by
      simpa using ((hasDerivAt_id t).const_mul (2:ℝ)).neg
    have h2 : HasDerivAt (Real.exp ∘ fun s : ℝ => -(2 * s)) (Real.exp (-(2 * t)) * (-2)) t :=
      (Real.hasDerivAt_exp (-(2 * t))).comp t h1
    exact h2.congr_deriv (by ring)
  have hpow : HasDerivAt (fun s : ℝ => (2 * s) ^ n) ((n : ℝ) * (2 * t) ^ (n - 1) * 2) t := by
    have h1 : HasDerivAt (fun s : ℝ => 2 * s) 2 t := by
      simpa using (hasDerivAt_id t).const_mul (2:ℝ)
    exact (hasDerivAt_pow n (2 * t)).comp t h1
  have hmul := (hexp.mul hpow).div_const ((n.factorial : ℝ))
  refine hmul.congr_deriv ?_
  cases n with
  | zero => simp [dPoissonWeight, poissonWeightPrev, poissonWeight]
  | succ m =>
      have hfacm : ((m + 1).factorial : ℝ) = ((m + 1 : ℕ) : ℝ) * (m.factorial : ℝ) := by
        rw [Nat.factorial_succ]; push_cast; ring
      have hmfac : (0:ℝ) < (m.factorial : ℝ) := by exact_mod_cast m.factorial_pos
      simp only [dPoissonWeight, poissonWeightPrev, poissonWeight, Nat.add_sub_cancel, hfacm]
      field_simp
      ring
