import Manhattan.Paper.Walk
import Manhattan.Paper.Poisson

/-!
# The continuous-time quenched kernel

`ck ω t x y = p_t^ω(x,y)` is the rate-two Poisson subordination of the jump
chain, as in `manuscript.tex:200-226`.  This file proves it is a doubly
stochastic kernel and satisfies the Chapman-Kolmogorov identity, the two
ingredients of the semigroup splitting in the proof of `prop:time`.
-/

open scoped BigOperators

namespace Manhattan.Paper

/-- The continuous-time quenched kernel, as a real number. -/
noncomputable def ck (ω : Environment) (t : ℝ) (x y : Site) : ℝ :=
  ∑' n : ℕ, poissonWeight t n * dk ω n x y

theorem summable_ck_terms (ω : Environment) {t : ℝ} (ht : 0 ≤ t) (x y : Site) :
    Summable fun n => poissonWeight t n * dk ω n x y := by
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg (poissonWeight_nonneg ht n) (dk_nonneg ω n x y)) (fun n => ?_)
    (summable_poissonWeight t)
  calc poissonWeight t n * dk ω n x y ≤ poissonWeight t n * 1 :=
        mul_le_mul_of_nonneg_left (dk_le_one ω n x y) (poissonWeight_nonneg ht n)
    _ = poissonWeight t n := mul_one _

theorem ck_nonneg (ω : Environment) {t : ℝ} (ht : 0 ≤ t) (x y : Site) : 0 ≤ ck ω t x y :=
  tsum_nonneg fun n => mul_nonneg (poissonWeight_nonneg ht n) (dk_nonneg ω n x y)

theorem ck_le_one (ω : Environment) {t : ℝ} (ht : 0 ≤ t) (x y : Site) : ck ω t x y ≤ 1 := by
  calc ck ω t x y ≤ ∑' n, poissonWeight t n :=
        Summable.tsum_le_tsum
          (fun n => by
            calc poissonWeight t n * dk ω n x y ≤ poissonWeight t n * 1 :=
                  mul_le_mul_of_nonneg_left (dk_le_one ω n x y) (poissonWeight_nonneg ht n)
              _ = poissonWeight t n := mul_one _)
          (summable_ck_terms ω ht x y) (summable_poissonWeight t)
    _ = 1 := tsum_poissonWeight t

theorem poissonWeight_zero_time (n : ℕ) : poissonWeight 0 n = if n = 0 then 1 else 0 := by
  cases n with
  | zero => simp [poissonWeight]
  | succ m => simp [poissonWeight]

@[simp] theorem ck_zero_time (ω : Environment) (x y : Site) :
    ck ω 0 x y = if x = y then 1 else 0 := by
  rw [ck, tsum_eq_single 0 fun n hn => by simp [poissonWeight_zero_time, hn]]
  simp [poissonWeight_zero_time]

/-! ### Both marginals -/

theorem summable_pair_row (ω : Environment) {t : ℝ} (ht : 0 ≤ t) (x : Site) :
    Summable fun q : ℕ × Site => poissonWeight t q.1 * dk ω q.1 x q.2 := by
  have hnn : (0 : ℕ × Site → ℝ) ≤ fun q : ℕ × Site => poissonWeight t q.1 * dk ω q.1 x q.2 := by
    intro q
    exact mul_nonneg (poissonWeight_nonneg ht q.1) (dk_nonneg ω q.1 x q.2)
  rw [summable_prod_of_nonneg hnn]
  refine ⟨fun n => ?_, ?_⟩
  · dsimp only
    exact (summable_dk_row ω n x).mul_left _
  · refine (summable_poissonWeight t).congr fun n => ?_
    dsimp only
    rw [tsum_mul_left, tsum_dk_row, mul_one]

theorem summable_pair_col (ω : Environment) {t : ℝ} (ht : 0 ≤ t) (y : Site) :
    Summable fun q : ℕ × Site => poissonWeight t q.1 * dk ω q.1 q.2 y := by
  have hnn : (0 : ℕ × Site → ℝ) ≤ fun q : ℕ × Site => poissonWeight t q.1 * dk ω q.1 q.2 y := by
    intro q
    exact mul_nonneg (poissonWeight_nonneg ht q.1) (dk_nonneg ω q.1 q.2 y)
  rw [summable_prod_of_nonneg hnn]
  refine ⟨fun n => ?_, ?_⟩
  · dsimp only
    exact (summable_dk_col ω n y).mul_left _
  · refine (summable_poissonWeight t).congr fun n => ?_
    dsimp only
    rw [tsum_mul_left, tsum_dk_col, mul_one]

theorem summable_ck_row (ω : Environment) {t : ℝ} (ht : 0 ≤ t) (x : Site) :
    Summable fun z => ck ω t x z := by
  have h : Summable fun q : Site × ℕ => poissonWeight t q.2 * dk ω q.2 x q.1 :=
    ((Equiv.prodComm Site ℕ).summable_iff
      (f := fun q : ℕ × Site => poissonWeight t q.1 * dk ω q.1 x q.2)).2
      (summable_pair_row ω ht x)
  exact h.prod

theorem summable_ck_col (ω : Environment) {t : ℝ} (ht : 0 ≤ t) (y : Site) :
    Summable fun z => ck ω t z y := by
  have h : Summable fun q : Site × ℕ => poissonWeight t q.2 * dk ω q.2 q.1 y :=
    ((Equiv.prodComm Site ℕ).summable_iff
      (f := fun q : ℕ × Site => poissonWeight t q.1 * dk ω q.1 q.2 y)).2
      (summable_pair_col ω ht y)
  exact h.prod

theorem tsum_ck_row (ω : Environment) {t : ℝ} (ht : 0 ≤ t) (x : Site) :
    ∑' z, ck ω t x z = 1 := by
  calc ∑' z : Site, ck ω t x z
      = ∑' (z : Site) (n : ℕ), poissonWeight t n * dk ω n x z := rfl
    _ = ∑' (n : ℕ) (z : Site), poissonWeight t n * dk ω n x z :=
        Summable.tsum_comm (summable_pair_row ω ht x)
    _ = ∑' n : ℕ, poissonWeight t n := by
        refine tsum_congr fun n => ?_
        rw [tsum_mul_left, tsum_dk_row, mul_one]
    _ = 1 := tsum_poissonWeight t

theorem tsum_ck_col (ω : Environment) {t : ℝ} (ht : 0 ≤ t) (y : Site) :
    ∑' z, ck ω t z y = 1 := by
  calc ∑' z : Site, ck ω t z y
      = ∑' (z : Site) (n : ℕ), poissonWeight t n * dk ω n z y := rfl
    _ = ∑' (n : ℕ) (z : Site), poissonWeight t n * dk ω n z y :=
        Summable.tsum_comm (summable_pair_col ω ht y)
    _ = ∑' n : ℕ, poissonWeight t n := by
        refine tsum_congr fun n => ?_
        rw [tsum_mul_left, tsum_dk_col, mul_one]
    _ = 1 := tsum_poissonWeight t

/-- Reversing the environment transposes the continuous-time kernel. -/
theorem ck_flipEnv (ω : Environment) (t : ℝ) (x y : Site) :
    ck ω t x y = ck (flipEnv ω) t y x :=
  tsum_congr fun n => by rw [dk_flipEnv]

/-! ### Chapman-Kolmogorov -/

/-- The rate-two Poisson weights convolve: `N_{a+b} = N_a + N'_b` in law. -/
theorem poissonWeight_convolution (a b : ℝ) (n : ℕ) :
    ∑ ij ∈ Finset.antidiagonal n, poissonWeight a ij.1 * poissonWeight b ij.2
      = poissonWeight (a + b) n := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => poissonWeight a i * poissonWeight b j) n]
  have hstep : ∀ k ∈ Finset.range n.succ,
      poissonWeight a k * poissonWeight b (n - k)
        = Real.exp (-(2 * (a + b))) / (n.factorial : ℝ) *
          ((2 * a) ^ k * (2 * b) ^ (n - k) * (n.choose k : ℝ)) := by
    intro k hk
    rw [Finset.mem_range, Nat.lt_succ_iff] at hk
    have hch : ((n.choose k : ℕ) : ℝ) * (k.factorial : ℝ) * (((n - k).factorial : ℕ) : ℝ)
        = (n.factorial : ℝ) := by
      exact_mod_cast congrArg (fun m : ℕ => (m : ℝ)) (Nat.choose_mul_factorial_mul_factorial hk)
    have hk0 : ((k.factorial : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 k.factorial_ne_zero
    have hnk0 : (((n - k).factorial : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (n - k).factorial_ne_zero
    rw [poissonWeight, poissonWeight]
    rw [show Real.exp (-(2 * a)) * (2 * a) ^ k / (k.factorial : ℝ) *
          (Real.exp (-(2 * b)) * (2 * b) ^ (n - k) / ((n - k).factorial : ℝ))
        = (Real.exp (-(2 * a)) * Real.exp (-(2 * b))) *
          ((2 * a) ^ k * (2 * b) ^ (n - k)) / ((k.factorial : ℝ) * ((n - k).factorial : ℝ)) from
      by ring]
    rw [← Real.exp_add, show -(2 * a) + -(2 * b) = -(2 * (a + b)) by ring]
    have hC : ((n.choose k : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.choose_pos hk).ne'
    rw [← hch]
    field_simp
  rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum, ← add_pow, poissonWeight]
  rw [show 2 * a + 2 * b = 2 * (a + b) by ring]
  ring

theorem tsum_prod_eq_tsum_antidiagonal {G : ℕ × ℕ → ℝ} (hG : Summable G) :
    ∑' q : ℕ × ℕ, G q = ∑' n : ℕ, ∑ ij ∈ Finset.antidiagonal n, G ij := by
  have hσ : Summable fun p : Σ n : ℕ, Finset.antidiagonal n => G (p.2 : ℕ × ℕ) :=
    (Finset.sigmaAntidiagonalEquivProd (A := ℕ)).summable_iff.2 hG
  have hrhs : ∀ n : ℕ, (∑ ij ∈ Finset.antidiagonal n, G ij)
      = ∑' ij : (Finset.antidiagonal n : Finset (ℕ × ℕ)), G ij :=
    fun n => (Finset.tsum_subtype (Finset.antidiagonal n) G).symm
  rw [tsum_congr hrhs, ← (Finset.sigmaAntidiagonalEquivProd (A := ℕ)).tsum_eq G]
  exact hσ.tsum_sigma' fun n => (hasSum_fintype _).summable

set_option maxHeartbeats 1000000 in
/-- The Chapman-Kolmogorov identity for the subordinated kernel. -/
theorem ck_chapman (ω : Environment) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (x y : Site) :
    ck ω (a + b) x y = ∑' z, ck ω a x z * ck ω b z y := by
  classical
  set G : ℕ × ℕ → ℝ :=
    fun q => poissonWeight a q.1 * poissonWeight b q.2 * dk ω (q.1 + q.2) x y with hGdef
  have hG0 : ∀ q, 0 ≤ G q := fun q =>
    mul_nonneg (mul_nonneg (poissonWeight_nonneg ha q.1) (poissonWeight_nonneg hb q.2))
      (dk_nonneg ω _ x y)
  have hGle : ∀ q : ℕ × ℕ, G q ≤ poissonWeight a q.1 * poissonWeight b q.2 := by
    intro q
    calc G q ≤ poissonWeight a q.1 * poissonWeight b q.2 * 1 :=
          mul_le_mul_of_nonneg_left (dk_le_one ω _ x y)
            (mul_nonneg (poissonWeight_nonneg ha q.1) (poissonWeight_nonneg hb q.2))
      _ = _ := mul_one _
  have hprodsummable : Summable fun q : ℕ × ℕ => poissonWeight a q.1 * poissonWeight b q.2 :=
    (summable_poissonWeight a).mul_of_nonneg (summable_poissonWeight b)
      (fun n => poissonWeight_nonneg ha n) (fun n => poissonWeight_nonneg hb n)
  have hG : Summable G := Summable.of_nonneg_of_le hG0 hGle hprodsummable
  set H : (ℕ × ℕ) × Site → ℝ :=
    fun p => poissonWeight a p.1.1 * dk ω p.1.1 x p.2 *
      (poissonWeight b p.1.2 * dk ω p.1.2 p.2 y) with hHdef
  have hH0 : (0 : (ℕ × ℕ) × Site → ℝ) ≤ H := by
    intro p
    exact mul_nonneg (mul_nonneg (poissonWeight_nonneg ha _) (dk_nonneg ω _ _ _))
      (mul_nonneg (poissonWeight_nonneg hb _) (dk_nonneg ω _ _ _))
  have hinner : ∀ q : ℕ × ℕ, (∑' z : Site, H (q, z)) = G q := by
    intro q
    have h1 : ∀ z : Site, H (q, z)
        = poissonWeight a q.1 * poissonWeight b q.2 * (dk ω q.1 x z * dk ω q.2 z y) := by
      intro z; simp only [hHdef]; ring
    rw [tsum_congr h1, tsum_mul_left, ← dk_chapman]
  have hHsummableFiber : ∀ q : ℕ × ℕ, Summable fun z : Site => H (q, z) := by
    intro q
    have hfun : (fun z : Site => H (q, z))
        = fun z => poissonWeight a q.1 * poissonWeight b q.2 * (dk ω q.1 x z * dk ω q.2 z y) := by
      funext z; simp only [hHdef]; ring
    rw [hfun]
    exact (summable_dk_mul ω q.1 q.2 x y).mul_left _
  have hH : Summable H := by
    rw [summable_prod_of_nonneg hH0]
    exact ⟨hHsummableFiber, hG.congr fun q => (hinner q).symm⟩
  have heval1 : ∑' p : (ℕ × ℕ) × Site, H p = ∑' q : ℕ × ℕ, G q := by
    rw [hH.tsum_prod]
    exact tsum_congr hinner
  have hswap : Summable fun p : Site × (ℕ × ℕ) => H ((Equiv.prodComm Site (ℕ × ℕ)) p) :=
    ((Equiv.prodComm Site (ℕ × ℕ)).summable_iff (f := H)).2 hH
  have heval2 : ∑' p : (ℕ × ℕ) × Site, H p = ∑' z : Site, ck ω a x z * ck ω b z y := by
    rw [← (Equiv.prodComm Site (ℕ × ℕ)).tsum_eq H, hswap.tsum_prod]
    refine tsum_congr fun z => ?_
    have hfg : Summable fun q : ℕ × ℕ =>
        (poissonWeight a q.1 * dk ω q.1 x z) * (poissonWeight b q.2 * dk ω q.2 z y) :=
      (summable_ck_terms ω ha x z).mul_of_nonneg (summable_ck_terms ω hb z y)
        (fun n => mul_nonneg (poissonWeight_nonneg ha n) (dk_nonneg ω n x z))
        (fun n => mul_nonneg (poissonWeight_nonneg hb n) (dk_nonneg ω n z y))
    exact ((summable_ck_terms ω ha x z).tsum_mul_tsum (summable_ck_terms ω hb z y) hfg).symm
  rw [← heval2, heval1, tsum_prod_eq_tsum_antidiagonal hG]
  refine (tsum_congr fun n => ?_).symm
  rw [← poissonWeight_convolution a b n, Finset.sum_mul]
  refine Finset.sum_congr rfl fun ij hij => ?_
  rw [Finset.mem_antidiagonal] at hij
  simp only [hGdef, hij]
