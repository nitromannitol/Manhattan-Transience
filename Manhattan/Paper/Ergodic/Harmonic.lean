/-
Divergence of the harmonic series in the extended nonnegative reals, where a
divergent series is simply equal to `⊤`.
-/
import Mathlib

namespace Manhattan.Paper.Ergodic

open scoped NNReal ENNReal

/-- The scaled harmonic series diverges. -/
theorem tsum_harmonic_eq_top :
    ∑' m : ℕ, (1 / (4 * (m + 1)) : ℝ≥0∞) = ⊤ := by
  have hcast : ∑' m : ℕ, ((1 / (4 * ((m : ℝ≥0) + 1)) : ℝ≥0) : ℝ≥0∞)
      = ∑' m : ℕ, (1 / (4 * (m + 1)) : ℝ≥0∞) := by
    refine tsum_congr fun m => ?_
    rw [ENNReal.coe_div (by positivity)]
    push_cast
    rfl
  rw [← hcast]
  by_contra hne
  have hsummable : Summable (fun m : ℕ => (1 / (4 * ((m : ℝ≥0) + 1)) : ℝ≥0)) :=
    ENNReal.tsum_coe_ne_top_iff_summable.mp hne
  have hreal : Summable (fun m : ℕ => ((1 / (4 * ((m : ℝ≥0) + 1)) : ℝ≥0) : ℝ)) :=
    NNReal.summable_coe.mpr hsummable
  have hshift : Summable (fun m : ℕ => (1 / ((m : ℝ) + 1))) := by
    have h4 := hreal.mul_left (4 : ℝ)
    refine h4.congr fun m => ?_
    push_cast
    have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    field_simp
  -- shifting the index by one contradicts divergence of the harmonic series
  have : Summable (fun n : ℕ => 1 / ((n : ℝ))) := by
    refine (summable_nat_add_iff (f := fun n : ℕ => 1 / ((n : ℝ))) 1).mp ?_
    refine hshift.congr fun m => ?_
    push_cast
    ring
  exact Real.not_summable_one_div_natCast this

end Manhattan.Paper.Ergodic
