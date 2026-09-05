import Manhattan.Paper.HeatKernel

/-!
# The time derivative of the return probability

This is the second half of `manuscript.tex:1449-1480` (`prop:time`,
equation `eq:time-derivative`).  The Poisson clock supplies the `t^{-1/2}`
gain: `tsum_abs_dPoissonWeight_le` is the manuscript's `E|N/t - 2| ≤ √(2/t)`,
proved from the exact Poisson mean and variance, and the heat-kernel bound of
`Manhattan.Paper.HeatKernel` supplies the remaining `t^{-1}` after the
semigroup is split at `t/2`.
-/

open scoped BigOperators

namespace Manhattan.Paper


theorem poissonWeight_succ_mul (s : ℝ) (m : ℕ) :
    ((m : ℝ) + 1) * poissonWeight s (m + 1) = 2 * s * poissonWeight s m := by
  have hm : (0:ℝ) < (m.factorial : ℝ) := by exact_mod_cast m.factorial_pos
  rw [poissonWeight, poissonWeight, Nat.factorial_succ]
  push_cast
  field_simp
  ring

theorem summable_nat_mul_poissonWeight (s : ℝ) :
    Summable fun n : ℕ => (n : ℝ) * poissonWeight s n := by
  refine (summable_nat_add_iff 1).1 ?_
  refine ((summable_poissonWeight s).mul_left (2 * s)).congr fun m => ?_
  rw [← poissonWeight_succ_mul s m]
  push_cast
  ring

theorem tsum_nat_mul_poissonWeight (s : ℝ) :
    ∑' n : ℕ, (n : ℝ) * poissonWeight s n = 2 * s := by
  rw [(summable_nat_mul_poissonWeight s).tsum_eq_zero_add]
  have h0 : ((0:ℕ) : ℝ) * poissonWeight s 0 = 0 := by simp
  rw [h0, zero_add]
  have hterm : ∀ m : ℕ, ((m + 1 : ℕ) : ℝ) * poissonWeight s (m + 1)
      = 2 * s * poissonWeight s m := by
    intro m
    rw [← poissonWeight_succ_mul s m]
    push_cast
    ring
  rw [tsum_congr hterm, tsum_mul_left, tsum_poissonWeight, mul_one]

theorem summable_nat_sq_mul_poissonWeight (s : ℝ) :
    Summable fun n : ℕ => (n : ℝ) ^ 2 * poissonWeight s n := by
  refine (summable_nat_add_iff 1).1 ?_
  refine (((summable_nat_mul_poissonWeight s).add (summable_poissonWeight s)).mul_left
    (2 * s)).congr fun m => ?_
  have h := poissonWeight_succ_mul s m
  have : ((m + 1 : ℕ) : ℝ) ^ 2 * poissonWeight s (m + 1)
      = ((m : ℝ) + 1) * (((m : ℝ) + 1) * poissonWeight s (m + 1)) := by push_cast; ring
  rw [this, h]
  ring

theorem tsum_nat_sq_mul_poissonWeight (s : ℝ) :
    ∑' n : ℕ, (n : ℝ) ^ 2 * poissonWeight s n = (2 * s) ^ 2 + 2 * s := by
  rw [(summable_nat_sq_mul_poissonWeight s).tsum_eq_zero_add]
  have h0 : ((0:ℕ) : ℝ) ^ 2 * poissonWeight s 0 = 0 := by simp
  rw [h0, zero_add]
  have hterm : ∀ m : ℕ, ((m + 1 : ℕ) : ℝ) ^ 2 * poissonWeight s (m + 1)
      = 2 * s * ((m : ℝ) * poissonWeight s m) + 2 * s * poissonWeight s m := by
    intro m
    have h := poissonWeight_succ_mul s m
    have h2 : ((m + 1 : ℕ) : ℝ) ^ 2 * poissonWeight s (m + 1)
        = ((m : ℝ) + 1) * (((m : ℝ) + 1) * poissonWeight s (m + 1)) := by push_cast; ring
    rw [h2, h]
    ring
  rw [tsum_congr hterm, Summable.tsum_add
    ((summable_nat_mul_poissonWeight s).mul_left (2 * s))
    ((summable_poissonWeight s).mul_left (2 * s)), tsum_mul_left, tsum_mul_left,
    tsum_nat_mul_poissonWeight, tsum_poissonWeight]
  ring

theorem summable_centered_sq (s : ℝ) :
    Summable fun n : ℕ => poissonWeight s n * ((n : ℝ) - 2 * s) ^ 2 := by
  refine (((summable_nat_sq_mul_poissonWeight s).sub
    ((summable_nat_mul_poissonWeight s).mul_left (2 * (2 * s)))).add
    ((summable_poissonWeight s).mul_left ((2 * s) ^ 2))).congr fun n => ?_
  ring

theorem tsum_centered_sq (s : ℝ) :
    ∑' n : ℕ, poissonWeight s n * ((n : ℝ) - 2 * s) ^ 2 = 2 * s := by
  have hterm : ∀ n : ℕ, poissonWeight s n * ((n : ℝ) - 2 * s) ^ 2
      = ((n : ℝ) ^ 2 * poissonWeight s n - 2 * (2 * s) * ((n : ℝ) * poissonWeight s n))
        + (2 * s) ^ 2 * poissonWeight s n := by
    intro n; ring
  rw [tsum_congr hterm, Summable.tsum_add
      ((summable_nat_sq_mul_poissonWeight s).sub
        ((summable_nat_mul_poissonWeight s).mul_left (2 * (2 * s))))
      ((summable_poissonWeight s).mul_left ((2 * s) ^ 2)),
    Summable.tsum_sub (summable_nat_sq_mul_poissonWeight s)
      ((summable_nat_mul_poissonWeight s).mul_left (2 * (2 * s))),
    tsum_mul_left, tsum_mul_left, tsum_nat_sq_mul_poissonWeight, tsum_nat_mul_poissonWeight,
    tsum_poissonWeight]
  ring

theorem dPoissonWeight_eq_mul {s : ℝ} (hs : 0 < s) (n : ℕ) :
    dPoissonWeight s n = poissonWeight s n * ((n : ℝ) / s - 2) := by
  cases n with
  | zero => simp [dPoissonWeight, poissonWeightPrev]; ring
  | succ m =>
      have h := poissonWeight_succ_mul s m
      have hkey : poissonWeight s (m + 1) * (((m : ℝ) + 1) / s) = 2 * poissonWeight s m := by
        field_simp
        linarith [h]
      simp only [dPoissonWeight, poissonWeightPrev]
      push_cast
      linear_combination -hkey

theorem summable_poissonWeightPrev (s : ℝ) : Summable (poissonWeightPrev s) := by
  refine (summable_nat_add_iff 1).1 ?_
  exact (summable_poissonWeight s).congr fun m => rfl

theorem summable_abs_dPoissonWeight {s : ℝ} (hs : 0 ≤ s) :
    Summable fun n => |dPoissonWeight s n| := by
  refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_)
    (((summable_poissonWeightPrev s).add (summable_poissonWeight s)).mul_left 2)
  have h1 : 0 ≤ poissonWeightPrev s n := poissonWeightPrev_nonneg hs n
  have h2 : 0 ≤ poissonWeight s n := poissonWeight_nonneg hs n
  rw [dPoissonWeight, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  have h3 : |poissonWeightPrev s n - poissonWeight s n|
      ≤ poissonWeightPrev s n + poissonWeight s n := by
    rw [abs_le]; constructor <;> linarith
  linarith

theorem tsum_abs_dPoissonWeight_le {s : ℝ} (hs : 0 < s) :
    ∑' n, |dPoissonWeight s n| ≤ Real.sqrt (2 / s) := by
  have hs0 : (0:ℝ) ≤ s := hs.le
  have hsq : ∀ n : ℕ, Real.sqrt (poissonWeight s n) * Real.sqrt (poissonWeight s n)
      = poissonWeight s n := fun n => Real.mul_self_sqrt (poissonWeight_nonneg hs0 n)
  have hprod : ∀ n : ℕ, Real.sqrt (poissonWeight s n)
      * (Real.sqrt (poissonWeight s n) * |(n : ℝ) / s - 2|) = |dPoissonWeight s n| := by
    intro n
    rw [show Real.sqrt (poissonWeight s n) * (Real.sqrt (poissonWeight s n)
        * |(n : ℝ) / s - 2|)
      = (Real.sqrt (poissonWeight s n) * Real.sqrt (poissonWeight s n)) * |(n : ℝ) / s - 2| from
      by ring, hsq n, dPoissonWeight_eq_mul hs n, abs_mul,
      abs_of_nonneg (poissonWeight_nonneg hs0 n)]
  have hbsq : ∀ n : ℕ, (Real.sqrt (poissonWeight s n) * |(n : ℝ) / s - 2|) ^ 2
      = poissonWeight s n * ((n : ℝ) - 2 * s) ^ 2 / s ^ 2 := by
    intro n
    rw [mul_pow, Real.sq_sqrt (poissonWeight_nonneg hs0 n), sq_abs]
    field_simp
  have hb : Summable fun n : ℕ => (Real.sqrt (poissonWeight s n) * |(n : ℝ) / s - 2|) ^ 2 :=
    ((summable_centered_sq s).div_const (s ^ 2)).congr fun n => (hbsq n).symm
  have ha : Summable fun n : ℕ => Real.sqrt (poissonWeight s n) ^ 2 :=
    (summable_poissonWeight s).congr fun n => (Real.sq_sqrt (poissonWeight_nonneg hs0 n)).symm
  have hab : Summable fun n : ℕ => Real.sqrt (poissonWeight s n)
      * (Real.sqrt (poissonWeight s n) * |(n : ℝ) / s - 2|) :=
    (summable_abs_dPoissonWeight hs0).congr fun n => (hprod n).symm
  have hcs := tsum_mul_le_sqrt_mul_sqrt (fun n : ℕ => Real.sqrt (poissonWeight s n))
    (fun n : ℕ => Real.sqrt (poissonWeight s n) * |(n : ℝ) / s - 2|)
    (fun n => Real.sqrt_nonneg _)
    (fun n => mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)) hab ha hb
  rw [tsum_congr hprod] at hcs
  have hA : (∑' n : ℕ, Real.sqrt (poissonWeight s n) ^ 2) = 1 := by
    rw [tsum_congr fun n => Real.sq_sqrt (poissonWeight_nonneg hs0 n), tsum_poissonWeight]
  have hB : (∑' n : ℕ, (Real.sqrt (poissonWeight s n) * |(n : ℝ) / s - 2|) ^ 2) = 2 / s := by
    rw [tsum_congr hbsq, tsum_div_const, tsum_centered_sq]
    field_simp
  rw [hA, hB, Real.sqrt_one, one_mul] at hcs
  exact hcs

/-! ### The generator applied to the subordinated kernel -/

/-- The time derivative of `p_t^ω(x, ·)`, as the generator applied at `x`. -/
noncomputable def dck (ω : Environment) (t : ℝ) (x z : Site) : ℝ :=
  ck ω t (directedNeighbor ω x Axis.horizontal) z
    + ck ω t (directedNeighbor ω x Axis.vertical) z - 2 * ck ω t x z

theorem tsum_dPoissonWeight_mul_dk (ω : Environment) {t : ℝ} (ht : 0 ≤ t) (x z : Site) :
    (∑' n, dPoissonWeight t n * dk ω n x z) = dck ω t x z := by
  have hsplit : ∀ n : ℕ, dPoissonWeight t n * dk ω n x z
      = 2 * (poissonWeightPrev t n * dk ω n x z) - 2 * (poissonWeight t n * dk ω n x z) := by
    intro n; rw [dPoissonWeight]; ring
  have hs1 : Summable fun n => poissonWeightPrev t n * dk ω n x z :=
    summable_poissonWeightPrev_mul ω ht x z
  have hs2 : Summable fun n => poissonWeight t n * dk ω n x z := summable_ck_terms ω ht x z
  rw [tsum_congr hsplit, Summable.tsum_sub (hs1.mul_left 2) (hs2.mul_left 2),
    tsum_mul_left, tsum_mul_left]
  have hshift : (∑' n, poissonWeightPrev t n * dk ω n x z)
      = 2⁻¹ * (ck ω t (directedNeighbor ω x Axis.horizontal) z
        + ck ω t (directedNeighbor ω x Axis.vertical) z) := by
    rw [hs1.tsum_eq_zero_add]
    have hzero : poissonWeightPrev t 0 * dk ω 0 x z = 0 := by simp [poissonWeightPrev]
    rw [hzero, zero_add]
    have hterm : ∀ m : ℕ, poissonWeightPrev t (m + 1) * dk ω (m + 1) x z
        = 2⁻¹ * (poissonWeight t m * dk ω m (directedNeighbor ω x Axis.horizontal) z)
          + 2⁻¹ * (poissonWeight t m * dk ω m (directedNeighbor ω x Axis.vertical) z) := by
      intro m
      show poissonWeight t m * dk ω (m + 1) x z = _
      rw [dk_succ]; ring
    rw [tsum_congr hterm,
      Summable.tsum_add ((summable_ck_terms ω ht _ z).mul_left _)
        ((summable_ck_terms ω ht _ z).mul_left _), tsum_mul_left, tsum_mul_left]
    simp only [ck]
    ring
  rw [hshift, dck]
  simp only [ck]
  ring

/-! ### Row sums with a general weight -/

theorem summable_pair_weight_row (c : ℕ → ℝ) (hc0 : ∀ n, 0 ≤ c n) (hc : Summable c)
    (ω : Environment) (x : Site) :
    Summable fun q : ℕ × Site => c q.1 * dk ω q.1 x q.2 := by
  have hnn : (0 : ℕ × Site → ℝ) ≤ fun q : ℕ × Site => c q.1 * dk ω q.1 x q.2 := by
    intro q
    exact mul_nonneg (hc0 q.1) (dk_nonneg ω q.1 x q.2)
  rw [summable_prod_of_nonneg hnn]
  refine ⟨fun n => ?_, ?_⟩
  · dsimp only
    exact (summable_dk_row ω n x).mul_left _
  · refine hc.congr fun n => ?_
    dsimp only
    rw [tsum_mul_left, tsum_dk_row, mul_one]

theorem summable_weight_row (c : ℕ → ℝ) (hc0 : ∀ n, 0 ≤ c n) (hc : Summable c)
    (ω : Environment) (x : Site) :
    Summable fun z : Site => ∑' n : ℕ, c n * dk ω n x z := by
  have h : Summable fun q : Site × ℕ => c q.2 * dk ω q.2 x q.1 :=
    ((Equiv.prodComm Site ℕ).summable_iff
      (f := fun q : ℕ × Site => c q.1 * dk ω q.1 x q.2)).2
      (summable_pair_weight_row c hc0 hc ω x)
  exact h.prod

theorem tsum_weight_row (c : ℕ → ℝ) (hc0 : ∀ n, 0 ≤ c n) (hc : Summable c)
    (ω : Environment) (x : Site) :
    (∑' z : Site, ∑' n : ℕ, c n * dk ω n x z) = ∑' n, c n := by
  calc ∑' (z : Site) (n : ℕ), c n * dk ω n x z
      = ∑' (n : ℕ) (z : Site), c n * dk ω n x z :=
        Summable.tsum_comm (summable_pair_weight_row c hc0 hc ω x)
    _ = ∑' n, c n := tsum_congr fun n => by rw [tsum_mul_left, tsum_dk_row, mul_one]

theorem abs_dck_le_tsum (ω : Environment) {s : ℝ} (hs : 0 < s) (x z : Site) :
    |dck ω s x z| ≤ ∑' n, |dPoissonWeight s n| * dk ω n x z := by
  have habsS : Summable fun n => |dPoissonWeight s n| := summable_abs_dPoissonWeight hs.le
  rw [← tsum_dPoissonWeight_mul_dk ω hs.le x z]
  have hnormsum : Summable fun n => ‖dPoissonWeight s n * dk ω n x z‖ := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) habsS
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (dk_nonneg ω n x z)]
    calc |dPoissonWeight s n| * dk ω n x z ≤ |dPoissonWeight s n| * 1 :=
          mul_le_mul_of_nonneg_left (dk_le_one ω n x z) (abs_nonneg _)
      _ = _ := mul_one _
  have h := norm_tsum_le_tsum_norm hnormsum
  rw [Real.norm_eq_abs] at h
  refine h.trans (le_of_eq (tsum_congr fun n => ?_))
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (dk_nonneg ω n x z)]

theorem summable_abs_dck (ω : Environment) {s : ℝ} (hs : 0 < s) (x : Site) :
    Summable fun z : Site => |dck ω s x z| :=
  Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (abs_dck_le_tsum ω hs x)
    (summable_weight_row _ (fun _ => abs_nonneg _) (summable_abs_dPoissonWeight hs.le) ω x)

/-- The `ℓ¹` bound on one row of the generator applied to the semigroup:
`sup_x ∑_y |(G P_s)(x,y)| ≤ √(2/s)`. -/
theorem tsum_abs_dck_le (ω : Environment) {s : ℝ} (hs : 0 < s) (x : Site) :
    (∑' z, |dck ω s x z|) ≤ Real.sqrt (2 / s) := by
  have habs0 : ∀ n : ℕ, 0 ≤ |dPoissonWeight s n| := fun n => abs_nonneg _
  have habsS : Summable fun n => |dPoissonWeight s n| := summable_abs_dPoissonWeight hs.le
  calc (∑' z, |dck ω s x z|) ≤ ∑' z : Site, ∑' n : ℕ, |dPoissonWeight s n| * dk ω n x z :=
        Summable.tsum_le_tsum (abs_dck_le_tsum ω hs x) (summable_abs_dck ω hs x)
          (summable_weight_row _ habs0 habsS ω x)
    _ = ∑' n, |dPoissonWeight s n| := tsum_weight_row _ habs0 habsS ω x
    _ ≤ Real.sqrt (2 / s) := tsum_abs_dPoissonWeight_le hs

/-! ### Splitting the semigroup at half the time -/

theorem dck_chapman (ω : Environment) {s : ℝ} (hs : 0 ≤ s) (x y : Site) :
    dck ω (s + s) x y = ∑' z, dck ω s x z * ck ω s z y := by
  have hsum : ∀ w : Site, Summable fun z => ck ω s w z * ck ω s z y := by
    intro w
    refine Summable.of_nonneg_of_le
      (fun z => mul_nonneg (ck_nonneg ω hs w z) (ck_nonneg ω hs z y)) (fun z => ?_)
      (summable_ck_row ω hs w)
    nlinarith [ck_nonneg ω hs w z, ck_le_one ω hs z y, ck_nonneg ω hs z y]
  have hexp : ∀ z : Site, dck ω s x z * ck ω s z y
      = (ck ω s (directedNeighbor ω x Axis.horizontal) z * ck ω s z y
          + ck ω s (directedNeighbor ω x Axis.vertical) z * ck ω s z y)
        - 2 * (ck ω s x z * ck ω s z y) := by
    intro z; rw [dck]; ring
  rw [tsum_congr hexp,
    Summable.tsum_sub ((hsum _).add (hsum _)) ((hsum x).mul_left 2),
    Summable.tsum_add (hsum _) (hsum _), tsum_mul_left,
    ← ck_chapman ω hs hs, ← ck_chapman ω hs hs, ← ck_chapman ω hs hs, dck]

theorem abs_tsum_le {ι : Type*} (f g : ι → ℝ) (hf : Summable fun i => |f i|)
    (hg : Summable g) (h : ∀ i, |f i| ≤ g i) : |∑' i, f i| ≤ ∑' i, g i := by
  have h1 : |∑' i, f i| ≤ ∑' i, |f i| := by
    have h2 := norm_tsum_le_tsum_norm (f := f) (by simpa only [Real.norm_eq_abs] using hf)
    simpa only [Real.norm_eq_abs] using h2
  exact h1.trans (Summable.tsum_le_tsum h hf hg)

set_option maxHeartbeats 1000000 in
theorem abs_dck_le_sharp (ω : Environment) {t : ℝ} (ht : 0 < t) (x y : Site) :
    |dck ω t x y| ≤ 4 / (Real.sqrt t * (2 + t)) := by
  have hs : (0:ℝ) < t / 2 := by linarith
  have htne : t ≠ 0 := ne_of_gt ht
  have hts : t / 2 + t / 2 = t := by ring
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have hsq : Real.sqrt (2 / (t / 2)) = 2 / Real.sqrt t := by
    have hrw : (2:ℝ) / (t / 2) = 4 / t := by field_simp; ring
    rw [hrw, Real.sqrt_div (by norm_num : (0:ℝ) ≤ 4), h4]
  have hsumF : Summable fun z => |dck ω (t / 2) x z| := summable_abs_dck ω hs x
  have hbnd : ∀ z : Site, |dck ω (t / 2) x z * ck ω (t / 2) z y|
      ≤ |dck ω (t / 2) x z| * (1 / (1 + t / 2)) := by
    intro z
    rw [abs_mul, abs_of_nonneg (ck_nonneg ω hs.le z y)]
    exact mul_le_mul_of_nonneg_left (ck_le_one_div ω hs.le z y) (abs_nonneg _)
  have hsumG : Summable fun z => |dck ω (t / 2) x z * ck ω (t / 2) z y| :=
    Summable.of_nonneg_of_le (fun z => abs_nonneg _) hbnd (hsumF.mul_right (1 / (1 + t / 2)))
  have hstep : |dck ω t x y| ≤ (∑' z, |dck ω (t / 2) x z|) * (1 / (1 + t / 2)) := by
    have hsplit : dck ω t x y = ∑' z, dck ω (t / 2) x z * ck ω (t / 2) z y := by
      have h := dck_chapman ω hs.le x y
      rwa [hts] at h
    rw [hsplit, ← tsum_mul_right]
    exact abs_tsum_le (fun z : Site => dck ω (t / 2) x z * ck ω (t / 2) z y)
      (fun z : Site => |dck ω (t / 2) x z| * (1 / (1 + t / 2))) hsumG
      (hsumF.mul_right (1 / (1 + t / 2))) hbnd
  have hsqrtpos : (0:ℝ) < Real.sqrt t := Real.sqrt_pos.2 ht
  have hfirst : (∑' z, |dck ω (t / 2) x z|) ≤ 2 / Real.sqrt t := by
    have h := tsum_abs_dck_le ω hs x
    rwa [hsq] at h
  refine hstep.trans ?_
  calc (∑' z, |dck ω (t / 2) x z|) * (1 / (1 + t / 2))
      ≤ (2 / Real.sqrt t) * (1 / (1 + t / 2)) :=
        mul_le_mul_of_nonneg_right hfirst (by positivity)
    _ = 4 / (Real.sqrt t * (2 + t)) := by field_simp; ring

/-- Equation `eq:time-derivative` of `manuscript.tex`, quenched form. -/
theorem abs_dck_le_paper (ω : Environment) {t : ℝ} (ht : 0 < t) (x y : Site) :
    |dck ω t x y| ≤ 2 / (Real.sqrt t * (1 + t / 4)) := by
  refine (abs_dck_le_sharp ω ht x y).trans ?_
  have hsqrtpos : (0:ℝ) < Real.sqrt t := Real.sqrt_pos.2 ht
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hsqrtpos, ht]

/-- The `8 t^{-3/2}` form of `eq:time-derivative`. -/
theorem abs_dck_le_pow (ω : Environment) {t : ℝ} (ht : 0 < t) (x y : Site) :
    |dck ω t x y| ≤ 8 / (t * Real.sqrt t) := by
  refine (abs_dck_le_paper ω ht x y).trans ?_
  have hsqrtpos : (0:ℝ) < Real.sqrt t := Real.sqrt_pos.2 ht
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hsqrtpos, ht]
