import Manhattan.Paper.L2Decay

/-!
# The deterministic heat-kernel bound

This is the first half of `manuscript.tex:1433-1447` (`prop:time`,
equation `eq:heat-kernel`):

  `p_t^ω(x,y) ≤ 2/(t+2)` for every deterministic Manhattan orientation `ω`,
  all `x, y ∈ ℤ²` and all `t ≥ 0`.

The proof is the manuscript's: split the semigroup at `t/2`, apply
Cauchy-Schwarz, and use the `ℓ¹ → ℓ²` bound from the Nash differential
inequality on each factor, the second factor via the reversed environment.
The route proves the sharper `p_t^ω(x,y) ≤ 1/(1+t)`.
-/

open scoped BigOperators

namespace Manhattan.Paper

theorem summable_rowSq (ω : Environment) {t : ℝ} (ht : 0 ≤ t) (x : Site) :
    Summable fun z => ck ω t x z ^ 2 := by
  refine Summable.of_nonneg_of_le (fun z => sq_nonneg _) (fun z => ?_) (summable_ck_row ω ht x)
  nlinarith [ck_nonneg ω ht x z, ck_le_one ω ht x z]

/-- The `ℓ²` bound along a row, from the column bound for the reversed environment. -/
theorem rowSq_le (ω : Environment) {t : ℝ} (ht : 0 ≤ t) (x : Site) :
    (∑' z, ck ω t x z ^ 2) ≤ 1 / (1 + 2 * t) := by
  have h : ∀ z : Site, ck ω t x z ^ 2 = ck (flipEnv ω) t z x ^ 2 := fun z => by rw [ck_flipEnv]
  rw [tsum_congr h]
  exact colSq_le (flipEnv ω) ht x

/-- The sharp form of the deterministic heat-kernel bound. -/
theorem ck_le_one_div (ω : Environment) {t : ℝ} (ht : 0 ≤ t) (x y : Site) :
    ck ω t x y ≤ 1 / (1 + t) := by
  have hhalf : (0:ℝ) ≤ t / 2 := by linarith
  have hck : ck ω t x y = ∑' z, ck ω (t / 2) x z * ck ω (t / 2) z y := by
    have h := ck_chapman ω hhalf hhalf x y
    rwa [show t / 2 + t / 2 = t by ring] at h
  have hA : Summable fun z => ck ω (t / 2) x z ^ 2 := summable_rowSq ω hhalf x
  have hB : Summable fun z => ck ω (t / 2) z y ^ 2 := summable_colSq ω hhalf y
  have hAB : Summable fun z => ck ω (t / 2) x z * ck ω (t / 2) z y := by
    refine Summable.of_nonneg_of_le
      (fun z => mul_nonneg (ck_nonneg ω hhalf x z) (ck_nonneg ω hhalf z y)) (fun z => ?_)
      (summable_ck_row ω hhalf x)
    nlinarith [ck_nonneg ω hhalf x z, ck_le_one ω hhalf z y, ck_nonneg ω hhalf z y]
  have hcs := tsum_mul_le_sqrt_mul_sqrt (fun z => ck ω (t / 2) x z) (fun z => ck ω (t / 2) z y)
    (fun z => ck_nonneg ω hhalf x z) (fun z => ck_nonneg ω hhalf z y) hAB hA hB
  have hpos : (0:ℝ) < 1 + t := by linarith
  have hhalfeq : 1 + 2 * (t / 2) = 1 + t := by ring
  have hAle : (∑' z, ck ω (t / 2) x z ^ 2) ≤ 1 / (1 + t) := by
    have := rowSq_le ω hhalf x
    rwa [hhalfeq] at this
  have hBle : (∑' z, ck ω (t / 2) z y ^ 2) ≤ 1 / (1 + t) := by
    have := colSq_le ω hhalf y
    rwa [hhalfeq] at this
  have hsq : Real.sqrt (1 / (1 + t)) * Real.sqrt (1 / (1 + t)) = 1 / (1 + t) :=
    Real.mul_self_sqrt (by positivity)
  calc ck ω t x y = ∑' z, ck ω (t / 2) x z * ck ω (t / 2) z y := hck
    _ ≤ Real.sqrt (∑' z, ck ω (t / 2) x z ^ 2) * Real.sqrt (∑' z, ck ω (t / 2) z y ^ 2) := hcs
    _ ≤ Real.sqrt (1 / (1 + t)) * Real.sqrt (1 / (1 + t)) :=
        mul_le_mul (Real.sqrt_le_sqrt hAle) (Real.sqrt_le_sqrt hBle) (Real.sqrt_nonneg _)
          (Real.sqrt_nonneg _)
    _ = 1 / (1 + t) := hsq

/-- Equation `eq:heat-kernel` of `manuscript.tex`. -/
theorem ck_le_two_div (ω : Environment) {t : ℝ} (ht : 0 ≤ t) (x y : Site) :
    ck ω t x y ≤ 2 / (t + 2) := by
  refine (ck_le_one_div ω ht x y).trans ?_
  have h1 : (0:ℝ) < 1 + t := by linarith
  have h2 : (0:ℝ) < t + 2 := by linarith
  rw [div_le_div_iff₀ h1 h2]
  linarith

end Manhattan.Paper
