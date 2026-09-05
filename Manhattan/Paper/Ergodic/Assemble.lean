/-
Assembling Pólya in two dimensions.

Given the one dimensional count and the divergence of the harmonic series, the
planar Green series diverges.  The factor that decides it is the sharp bound
`16 ^ m ≤ 4 * m * centralBinom m ^ 2`: it makes the `m`-th even term at least
`1 / (4 * m)`, and that series diverges.  With Mathlib's weaker central
binomial bound the terms would only be `≳ 1 / m ^ 2` and the sum would converge,
which is exactly the difference between recurrence and transience.
-/
import Manhattan.Paper.Ergodic.Factorize
import Manhattan.Paper.Ergodic.CentralBinom

namespace Manhattan.Paper.Ergodic

open scoped NNReal ENNReal

/-- The even terms of the Green series dominate a multiple of the harmonic
series. -/
theorem harmonic_le_srwKernel
    (hcount : ∀ m : ℕ, oneDCount (2 * m) = Nat.centralBinom m) (m : ℕ) :
    (1 / (4 * (m + 1)) : ℝ≥0) ≤ srwKernel (2 * (m + 1)) := by
  have hsq : srwCount (2 * (m + 1)) 0 = (Nat.centralBinom (m + 1)) ^ 2 := by
    rw [srwCount_eq_sq, hcount (m + 1)]
  have hpow : ((4 : ℝ≥0))⁻¹ ^ (2 * (m + 1)) = ((16 : ℝ≥0))⁻¹ ^ (m + 1) := by
    rw [pow_mul]; norm_num
  rw [srwKernel, hsq, hpow]
  -- the integer bound `16 ^ (m+1) ≤ 4 * (m+1) * centralBinom (m+1) ^ 2`
  have hkey : (16 : ℝ≥0) ^ (m + 1)
      ≤ (4 * (m + 1) : ℝ≥0) * ((Nat.centralBinom (m + 1) : ℝ≥0)) ^ 2 := by
    have h := sixteen_pow_le (m + 1) (Nat.le_add_left 1 m)
    have := (Nat.cast_le (α := ℝ≥0)).mpr h
    push_cast at this
    convert this using 2
  have h16 : (0 : ℝ≥0) < 16 ^ (m + 1) := by positivity
  have hm : (0 : ℝ≥0) < 4 * (m + 1) := by positivity
  rw [div_le_iff₀ hm, inv_pow, ← div_eq_inv_mul, div_mul_eq_mul_div, le_div_iff₀ h16]
  calc (1 : ℝ≥0) * (16 : ℝ≥0) ^ (m + 1) = (16 : ℝ≥0) ^ (m + 1) := one_mul _
    _ ≤ (4 * (m + 1) : ℝ≥0) * ((Nat.centralBinom (m + 1) : ℝ≥0)) ^ 2 := hkey
    _ = (Nat.centralBinom (m + 1) : ℝ≥0) ^ 2 * (4 * (m + 1)) := mul_comm _ _
    _ = ((Nat.centralBinom (m + 1) ^ 2 : ℕ) : ℝ≥0) * (4 * (m + 1)) := by push_cast; rfl

/-- **Pólya's theorem in two dimensions**, given the one dimensional count and
the divergence of the harmonic series. -/
theorem simpleRandomWalkRecurrent_of
    (hcount : ∀ m : ℕ, oneDCount (2 * m) = Nat.centralBinom m)
    (hdiv : ∑' m : ℕ, (1 / (4 * (m + 1)) : ℝ≥0∞) = ⊤) :
    SimpleRandomWalkRecurrent := by
  have hinj : Function.Injective (fun m : ℕ => 2 * (m + 1)) := by
    intro a b hab; simpa using hab
  have hsub : ∑' m : ℕ, ((srwKernel (2 * (m + 1)) : ℝ≥0) : ℝ≥0∞)
      ≤ ∑' n : ℕ, ((srwKernel n : ℝ≥0) : ℝ≥0∞) :=
    ENNReal.tsum_comp_le_tsum_of_injective hinj _
  have hterm : ∀ m : ℕ, ((1 / (4 * (m + 1)) : ℝ≥0) : ℝ≥0∞)
      ≤ ((srwKernel (2 * (m + 1)) : ℝ≥0) : ℝ≥0∞) := by
    intro m
    exact_mod_cast ENNReal.coe_le_coe.mpr (harmonic_le_srwKernel hcount m)
  have hlow : ∑' m : ℕ, ((1 / (4 * (m + 1)) : ℝ≥0) : ℝ≥0∞)
      ≤ ∑' m : ℕ, ((srwKernel (2 * (m + 1)) : ℝ≥0) : ℝ≥0∞) :=
    ENNReal.tsum_le_tsum hterm
  have hcast : ∑' m : ℕ, ((1 / (4 * (m + 1)) : ℝ≥0) : ℝ≥0∞)
      = ∑' m : ℕ, (1 / (4 * (m + 1)) : ℝ≥0∞) := by
    refine tsum_congr fun m => ?_
    rw [ENNReal.coe_div (by positivity)]
    push_cast
    rfl
  rw [hcast, hdiv] at hlow
  exact top_le_iff.mp (le_trans hlow hsub)

end Manhattan.Paper.Ergodic
