import Manhattan.Paper.Nash
import Manhattan.Paper.ContKernel
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# The Nash differential inequality and the `ℓ²` decay

The Manhattan generator is `2(Q - I)`, whose symmetric part is the rate-two
simple-random-walk generator: `tsum_mul_directedNeighbor` is exactly that
statement in the form needed here, and it holds for every orientation.
Feeding the Nash inequality of `Manhattan.Paper.Nash` into

  `d/dt ∑_z p_t(z,y)² = - E(p_t(·,y))`

gives `∑_z p_t(z,y)² ≤ 1/(1+2t)`, the `ℓ¹ → ℓ²` half of `prop:time`.
-/

open scoped BigOperators

namespace Manhattan.Paper


theorem poissonWeight_le_scaled {s b : ℝ} (hs : 0 ≤ s) (hsb : s ≤ b) (n : ℕ) :
    poissonWeight s n ≤ Real.exp (2 * b) * poissonWeight b n := by
  have hfac : (0:ℝ) < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
  have h1 : Real.exp (-(2 * s)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; linarith
  have h2 : (2 * s) ^ n ≤ (2 * b) ^ n := by
    have hs2 : (0:ℝ) ≤ 2 * s := by linarith
    have hsb2 : 2 * s ≤ 2 * b := by linarith
    gcongr
  have hkey : Real.exp (-(2 * s)) * (2 * s) ^ n ≤ (2 * b) ^ n := by
    calc Real.exp (-(2 * s)) * (2 * s) ^ n ≤ 1 * (2 * s) ^ n :=
          mul_le_mul_of_nonneg_right h1 (pow_nonneg (by linarith) n)
      _ = (2 * s) ^ n := one_mul _
      _ ≤ (2 * b) ^ n := h2
  have hres : Real.exp (2 * b) * poissonWeight b n = (2 * b) ^ n / (n.factorial : ℝ) := by
    rw [poissonWeight, show Real.exp (2 * b) * (Real.exp (-(2 * b)) * (2 * b) ^ n
        / (n.factorial : ℝ))
      = Real.exp (2 * b) * Real.exp (-(2 * b)) * ((2 * b) ^ n / (n.factorial : ℝ)) from by ring,
      ← Real.exp_add]
    simp
  rw [hres, poissonWeight]
  gcongr

theorem ck_le_scaled (ω : Environment) {s b : ℝ} (hs : 0 ≤ s) (hsb : s ≤ b) (x y : Site) :
    ck ω s x y ≤ Real.exp (2 * b) * ck ω b x y := by
  have hb : 0 ≤ b := le_trans hs hsb
  calc ck ω s x y ≤ ∑' n, Real.exp (2 * b) * poissonWeight b n * dk ω n x y := by
        refine Summable.tsum_le_tsum (fun n => ?_) (summable_ck_terms ω hs x y)
          (((summable_ck_terms ω hb x y).mul_left (Real.exp (2 * b))).congr fun n => by ring)
        exact mul_le_mul_of_nonneg_right (poissonWeight_le_scaled hs hsb n) (dk_nonneg ω n x y)
    _ = Real.exp (2 * b) * ck ω b x y := by
        rw [ck, ← tsum_mul_left]
        exact tsum_congr fun n => by ring

theorem poissonWeight_le_bound {s b : ℝ} (hs : 0 ≤ s) (hsb : s ≤ b) (n : ℕ) :
    poissonWeight s n ≤ (2 * b) ^ n / (n.factorial : ℝ) := by
  have hfac : (0:ℝ) < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
  have h1 : Real.exp (-(2 * s)) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
  have hs2 : (0:ℝ) ≤ 2 * s := by linarith
  have hsb2 : 2 * s ≤ 2 * b := by linarith
  have h2 : (2 * s) ^ n ≤ (2 * b) ^ n := by gcongr
  rw [poissonWeight]
  gcongr
  calc Real.exp (-(2 * s)) * (2 * s) ^ n ≤ 1 * (2 * s) ^ n :=
        mul_le_mul_of_nonneg_right h1 (pow_nonneg hs2 n)
    _ = (2 * s) ^ n := one_mul _
    _ ≤ (2 * b) ^ n := h2

theorem poissonWeightPrev_nonneg {s : ℝ} (hs : 0 ≤ s) (n : ℕ) : 0 ≤ poissonWeightPrev s n := by
  cases n with
  | zero => simp [poissonWeightPrev]
  | succ m => exact poissonWeight_nonneg hs m

theorem poissonWeightPrev_le_bound {s b : ℝ} (hs : 0 ≤ s) (hsb : s ≤ b) (n : ℕ) :
    poissonWeightPrev s n ≤ (2 * b) ^ (n - 1) / ((n - 1).factorial : ℝ) := by
  cases n with
  | zero =>
      simp only [poissonWeightPrev]
      norm_num
  | succ m =>
      simpa [poissonWeightPrev] using poissonWeight_le_bound hs hsb m

theorem summable_factorial_bound (b : ℝ) :
    Summable fun n : ℕ => (2 * b) ^ (n - 1) / (((n - 1).factorial : ℕ) : ℝ) := by
  refine (summable_nat_add_iff 1).1 ?_
  simpa using Real.summable_pow_div_factorial (2 * b)

theorem summable_poissonWeightPrev_mul (ω : Environment) {t : ℝ} (ht : 0 ≤ t) (z y : Site) :
    Summable fun n => poissonWeightPrev t n * dk ω n z y := by
  refine (summable_nat_add_iff 1).1 ?_
  refine Summable.of_nonneg_of_le
    (fun m => mul_nonneg (poissonWeightPrev_nonneg ht _) (dk_nonneg ω _ z y)) (fun m => ?_)
    (summable_poissonWeight t)
  show poissonWeightPrev t (m + 1) * dk ω (m + 1) z y ≤ poissonWeight t m
  calc poissonWeightPrev t (m + 1) * dk ω (m + 1) z y
      = poissonWeight t m * dk ω (m + 1) z y := rfl
    _ ≤ poissonWeight t m * 1 :=
        mul_le_mul_of_nonneg_left (dk_le_one ω _ z y) (poissonWeight_nonneg ht m)
    _ = poissonWeight t m := mul_one _

set_option maxHeartbeats 1000000 in
theorem hasDerivAt_ck (ω : Environment) {t : ℝ} (ht : 0 < t) (z y : Site) :
    HasDerivAt (fun s => ck ω s z y)
      (ck ω t (directedNeighbor ω z Axis.horizontal) y
        + ck ω t (directedNeighbor ω z Axis.vertical) y - 2 * ck ω t z y) t := by
  set b : ℝ := t + 1 with hb
  have hb0 : (0:ℝ) < b := by simp [hb]; linarith
  set S : Set ℝ := Set.Ioo 0 b with hS
  have htS : t ∈ S := ⟨ht, by simp [hb]⟩
  have hu : Summable fun n : ℕ =>
      2 * ((2 * b) ^ n / ((n.factorial : ℕ) : ℝ)
        + (2 * b) ^ (n - 1) / (((n - 1).factorial : ℕ) : ℝ)) :=
    ((Real.summable_pow_div_factorial (2 * b)).add (summable_factorial_bound b)).mul_left 2
  have hderiv := hasDerivAt_tsum_of_isPreconnected (u := fun n : ℕ =>
      2 * ((2 * b) ^ n / ((n.factorial : ℕ) : ℝ)
        + (2 * b) ^ (n - 1) / (((n - 1).factorial : ℕ) : ℝ)))
    (g := fun (n : ℕ) (s : ℝ) => poissonWeight s n * dk ω n z y)
    (g' := fun (n : ℕ) (s : ℝ) => dPoissonWeight s n * dk ω n z y)
    hu isOpen_Ioo (convex_Ioo 0 b).isPreconnected
    (fun n s _ => (hasDerivAt_poissonWeight s n).mul_const _)
    (fun n s hs => by
      have hs0 : 0 ≤ s := le_of_lt hs.1
      have hsb : s ≤ b := le_of_lt hs.2
      have h1 : |dPoissonWeight s n| ≤ 2 * (poissonWeightPrev s n + poissonWeight s n) := by
        rw [dPoissonWeight, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
        have := abs_sub (poissonWeightPrev s n) (poissonWeight s n)
        have h2 : |poissonWeightPrev s n| = poissonWeightPrev s n :=
          abs_of_nonneg (poissonWeightPrev_nonneg hs0 n)
        have h3 : |poissonWeight s n| = poissonWeight s n :=
          abs_of_nonneg (poissonWeight_nonneg hs0 n)
        rw [h2, h3] at this
        linarith
      have h4 : ‖dPoissonWeight s n * dk ω n z y‖ ≤ |dPoissonWeight s n| := by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (dk_nonneg ω n z y)]
        calc |dPoissonWeight s n| * dk ω n z y ≤ |dPoissonWeight s n| * 1 :=
              mul_le_mul_of_nonneg_left (dk_le_one ω n z y) (abs_nonneg _)
          _ = _ := mul_one _
      refine h4.trans (h1.trans ?_)
      have hA := poissonWeight_le_bound hs0 hsb n
      have hB := poissonWeightPrev_le_bound hs0 hsb n
      linarith)
    htS (summable_ck_terms ω ht.le z y) htS
  refine hderiv.congr_deriv ?_
  have hsplit : ∀ n : ℕ, dPoissonWeight t n * dk ω n z y
      = 2 * (poissonWeightPrev t n * dk ω n z y) - 2 * (poissonWeight t n * dk ω n z y) := by
    intro n; rw [dPoissonWeight]; ring
  have hs1 : Summable fun n => poissonWeightPrev t n * dk ω n z y :=
    summable_poissonWeightPrev_mul ω ht.le z y
  have hs2 : Summable fun n => poissonWeight t n * dk ω n z y := summable_ck_terms ω ht.le z y
  rw [tsum_congr hsplit, Summable.tsum_sub (hs1.mul_left 2) (hs2.mul_left 2),
    tsum_mul_left, tsum_mul_left]
  have hshift : (∑' n, poissonWeightPrev t n * dk ω n z y)
      = 2⁻¹ * (ck ω t (directedNeighbor ω z Axis.horizontal) y
        + ck ω t (directedNeighbor ω z Axis.vertical) y) := by
    rw [hs1.tsum_eq_zero_add]
    have hzero : poissonWeightPrev t 0 * dk ω 0 z y = 0 := by simp [poissonWeightPrev]
    rw [hzero, zero_add]
    have hterm : ∀ m : ℕ, poissonWeightPrev t (m + 1) * dk ω (m + 1) z y
        = 2⁻¹ * (poissonWeight t m * dk ω m (directedNeighbor ω z Axis.horizontal) y)
          + 2⁻¹ * (poissonWeight t m * dk ω m (directedNeighbor ω z Axis.vertical) y) := by
      intro m
      show poissonWeight t m * dk ω (m + 1) z y = _
      rw [dk_succ]; ring
    rw [tsum_congr hterm,
      Summable.tsum_add ((summable_ck_terms ω ht.le _ y).mul_left _)
        ((summable_ck_terms ω ht.le _ y).mul_left _), tsum_mul_left, tsum_mul_left]
    simp only [ck]
    ring
  rw [hshift]
  show _ = ck ω t (directedNeighbor ω z Axis.horizontal) y
    + ck ω t (directedNeighbor ω z Axis.vertical) y - 2 * ck ω t z y
  simp only [ck]
  ring

theorem summable_mul_comp (c : Site → ℝ) (hc : Summable fun z => c z ^ 2) (e : Site ≃ Site) :
    Summable fun z => c z * c (e z) := by
  have hce : Summable fun z => c (e z) ^ 2 := (e.summable_iff (f := fun z => c z ^ 2)).2 hc
  have h1 : Summable fun z => (c z ^ 2 + c (e z) ^ 2) / 2 := (hc.add hce).div_const 2
  refine Summable.of_abs (Summable.of_nonneg_of_le (fun z => abs_nonneg _) (fun z => ?_) h1)
  have h2 : |c z * c (e z)| = |c z| * |c (e z)| := abs_mul _ _
  nlinarith [sq_abs (c z), sq_abs (c (e z)), two_mul_le_add_sq |c z| |c (e z)|, abs_nonneg (c z),
    abs_nonneg (c (e z))]

theorem step_add_flip (ω : Environment) (z : Site) (i : Axis) (c : Site → ℝ) :
    c (directedNeighbor ω z i) + c (directedNeighbor (flipEnv ω) z i)
      = c (z + basisStep i) + c (z - basisStep i) := by
  cases h : ω (lineAt z i) <;>
    simp [directedNeighbor, flipEnv, flipOrientation, h, Orientation.sign, sub_eq_add_neg,
      add_comm]

theorem tsum_mul_directedNeighbor (ω : Environment) (i : Axis) (c : Site → ℝ)
    (hc : Summable fun z => c z ^ 2) :
    ∑' z, c z * c (directedNeighbor ω z i) = ∑' z, c z * c (z + basisStep i) := by
  have hsum1 : Summable fun z => c z * c (directedNeighbor ω z i) :=
    summable_mul_comp c hc (stepEquiv ω i)
  have hsum2 : Summable fun z => c z * c (directedNeighbor (flipEnv ω) z i) :=
    summable_mul_comp c hc (stepEquiv (flipEnv ω) i)
  have hsum3 : Summable fun z => c z * c (z + basisStep i) :=
    summable_mul_comp c hc (Equiv.addRight (basisStep i))
  have hsum4 : Summable fun z => c z * c (z - basisStep i) :=
    summable_mul_comp c hc (Equiv.subRight (basisStep i))
  -- the two directed sums agree
  have hA : (∑' z, c z * c (directedNeighbor ω z i))
      = ∑' z, c z * c (directedNeighbor (flipEnv ω) z i) := by
    have h := (stepEquiv (flipEnv ω) i).tsum_eq fun z => c z * c (directedNeighbor ω z i)
    rw [← h]
    refine tsum_congr fun z => ?_
    have hz : directedNeighbor ω (directedNeighbor (flipEnv ω) z i) i = z := by
      have := directedNeighbor_flipEnv (flipEnv ω) z i
      rwa [flipEnv_flipEnv] at this
    simp only [stepEquiv_apply, hz]
    ring
  -- the backward shift agrees with the forward shift
  have hB : (∑' z, c z * c (z - basisStep i)) = ∑' z, c z * c (z + basisStep i) := by
    have h := (Equiv.addRight (basisStep i)).tsum_eq fun z => c z * c (z - basisStep i)
    rw [← h]
    refine tsum_congr fun z => ?_
    simp only [Equiv.coe_addRight, add_sub_cancel_right]
    ring
  have hcomb : (∑' z, c z * c (directedNeighbor ω z i))
      + ∑' z, c z * c (directedNeighbor (flipEnv ω) z i)
      = (∑' z, c z * c (z + basisStep i)) + ∑' z, c z * c (z - basisStep i) := by
    rw [← Summable.tsum_add hsum1 hsum2, ← Summable.tsum_add hsum3 hsum4]
    refine tsum_congr fun z => ?_
    linear_combination (c z) * step_add_flip ω z i c
  rw [hA] at hcomb ⊢
  rw [hB] at hcomb
  linarith

theorem energy_eq (c : Site → ℝ) (hc : Summable fun z => c z ^ 2) :
    energy c = 4 * (∑' z, c z ^ 2)
      - 2 * ((∑' z, c z * c (z + unitH)) + ∑' z, c z * c (z + unitV)) := by
  have key : ∀ v : Site, (∑' z, (c (z + v) - c z) ^ 2)
      = 2 * (∑' z, c z ^ 2) - 2 * ∑' z, c z * c (z + v) := by
    intro v
    have hshift : Summable fun z => c (z + v) ^ 2 :=
      ((Equiv.addRight v).summable_iff (f := fun z => c z ^ 2)).2 hc
    have hcross : Summable fun z => c z * c (z + v) := summable_mul_comp c hc (Equiv.addRight v)
    have hexp : ∀ z : Site, (c (z + v) - c z) ^ 2
        = (c (z + v) ^ 2 + c z ^ 2) - 2 * (c z * c (z + v)) := by intro z; ring
    rw [tsum_congr hexp, Summable.tsum_sub (hshift.add hc) (hcross.mul_left 2),
      Summable.tsum_add hshift hc, tsum_mul_left]
    have hsh : (∑' z, c (z + v) ^ 2) = ∑' z, c z ^ 2 :=
      (Equiv.addRight v).tsum_eq fun z => c z ^ 2
    rw [hsh]
    ring
  simp only [energy, gradH, gradV]
  rw [key unitH, key unitV]
  ring

/-! ### The differential inequality -/

theorem summable_colSq (ω : Environment) {t : ℝ} (ht : 0 ≤ t) (y : Site) :
    Summable fun z => ck ω t z y ^ 2 := by
  refine Summable.of_nonneg_of_le (fun z => sq_nonneg _) (fun z => ?_) (summable_ck_col ω ht y)
  nlinarith [ck_nonneg ω ht z y, ck_le_one ω ht z y]

theorem colSq_le_one (ω : Environment) {t : ℝ} (ht : 0 ≤ t) (y : Site) :
    (∑' z, ck ω t z y ^ 2) ≤ 1 := by
  calc (∑' z, ck ω t z y ^ 2) ≤ ∑' z, ck ω t z y :=
        Summable.tsum_le_tsum (fun z => by nlinarith [ck_nonneg ω ht z y, ck_le_one ω ht z y])
          (summable_colSq ω ht y) (summable_ck_col ω ht y)
    _ = 1 := tsum_ck_col ω ht y

theorem colSq_pos (ω : Environment) {t : ℝ} (ht : 0 ≤ t) (y : Site) :
    0 < ∑' z, ck ω t z y ^ 2 := by
  have h := (summable_ck_terms ω ht y y).le_tsum 0
    (fun j _ => mul_nonneg (poissonWeight_nonneg ht j) (dk_nonneg ω j y y))
  have h0 : poissonWeight t 0 * dk ω 0 y y = Real.exp (-(2 * t)) := by
    simp [poissonWeight]
  rw [h0] at h
  have hy : 0 < ck ω t y y := lt_of_lt_of_le (Real.exp_pos _) h
  have h2 := (summable_colSq ω ht y).le_tsum y (fun j _ => sq_nonneg _)
  nlinarith

theorem tsum_ode_eq (ω : Environment) {t : ℝ} (ht : 0 ≤ t) (y : Site) :
    (∑' z, 2 * ck ω t z y * (ck ω t (directedNeighbor ω z Axis.horizontal) y
      + ck ω t (directedNeighbor ω z Axis.vertical) y - 2 * ck ω t z y))
      = -(energy fun z => ck ω t z y) := by
  set c : Site → ℝ := fun z => ck ω t z y with hcdef
  have hc2 : Summable fun z => c z ^ 2 := summable_colSq ω ht y
  have hH : Summable fun z => c z * c (directedNeighbor ω z Axis.horizontal) :=
    summable_mul_comp c hc2 (stepEquiv ω Axis.horizontal)
  have hV : Summable fun z => c z * c (directedNeighbor ω z Axis.vertical) :=
    summable_mul_comp c hc2 (stepEquiv ω Axis.vertical)
  have hexp : ∀ z : Site, 2 * c z * (c (directedNeighbor ω z Axis.horizontal)
      + c (directedNeighbor ω z Axis.vertical) - 2 * c z)
      = (2 * (c z * c (directedNeighbor ω z Axis.horizontal))
        + 2 * (c z * c (directedNeighbor ω z Axis.vertical))) - 4 * c z ^ 2 := by
    intro z; ring
  rw [tsum_congr hexp,
    Summable.tsum_sub ((hH.mul_left 2).add (hV.mul_left 2)) (hc2.mul_left 4),
    Summable.tsum_add (hH.mul_left 2) (hV.mul_left 2), tsum_mul_left, tsum_mul_left,
    tsum_mul_left, tsum_mul_directedNeighbor ω Axis.horizontal c hc2,
    tsum_mul_directedNeighbor ω Axis.vertical c hc2, energy_eq c hc2]
  have hb1 : basisStep Axis.horizontal = unitH := rfl
  have hb2 : basisStep Axis.vertical = unitV := rfl
  rw [hb1, hb2]
  ring

set_option maxHeartbeats 1000000 in
theorem hasDerivAt_colL2 (ω : Environment) {t : ℝ} (ht : 0 < t) (y : Site) :
    HasDerivAt (fun s => ∑' z, ck ω s z y ^ 2) (-(energy fun z => ck ω t z y)) t := by
  set b : ℝ := t + 1 with hbdef
  have hb0 : (0:ℝ) < b := by rw [hbdef]; linarith
  have htb : t < b := by rw [hbdef]; linarith
  have hcolb : Summable fun z => ck ω b z y := summable_ck_col ω hb0.le y
  have hsh1 : Summable fun z => ck ω b (directedNeighbor ω z Axis.horizontal) y :=
    ((stepEquiv ω Axis.horizontal).summable_iff (f := fun z => ck ω b z y)).2 hcolb
  have hsh2 : Summable fun z => ck ω b (directedNeighbor ω z Axis.vertical) y :=
    ((stepEquiv ω Axis.vertical).summable_iff (f := fun z => ck ω b z y)).2 hcolb
  have hu : Summable fun z : Site => 2 * (Real.exp (2 * b) *
      (ck ω b (directedNeighbor ω z Axis.horizontal) y
        + ck ω b (directedNeighbor ω z Axis.vertical) y + 2 * ck ω b z y)) :=
    (((hsh1.add hsh2).add (hcolb.mul_left 2)).mul_left (Real.exp (2 * b))).mul_left 2
  have hderiv := hasDerivAt_tsum_of_isPreconnected
    (u := fun z : Site => 2 * (Real.exp (2 * b) *
      (ck ω b (directedNeighbor ω z Axis.horizontal) y
        + ck ω b (directedNeighbor ω z Axis.vertical) y + 2 * ck ω b z y)))
    (g := fun (z : Site) (s : ℝ) => ck ω s z y ^ 2)
    (g' := fun (z : Site) (s : ℝ) => 2 * ck ω s z y *
      (ck ω s (directedNeighbor ω z Axis.horizontal) y
        + ck ω s (directedNeighbor ω z Axis.vertical) y - 2 * ck ω s z y))
    hu isOpen_Ioo (convex_Ioo 0 b).isPreconnected
    (fun z s hs => by
      refine ((hasDerivAt_ck ω hs.1 z y).pow 2).congr_deriv ?_
      push_cast
      ring)
    (fun z s hs => by
      have hs0 : (0:ℝ) ≤ s := hs.1.le
      have hsb : s ≤ b := hs.2.le
      have hA := ck_le_scaled ω hs0 hsb (directedNeighbor ω z Axis.horizontal) y
      have hB := ck_le_scaled ω hs0 hsb (directedNeighbor ω z Axis.vertical) y
      have hC := ck_le_scaled ω hs0 hsb z y
      have h0 := ck_nonneg ω hs0 z y
      have h1 := ck_le_one ω hs0 z y
      have hA0 := ck_nonneg ω hs0 (directedNeighbor ω z Axis.horizontal) y
      have hB0 := ck_nonneg ω hs0 (directedNeighbor ω z Axis.vertical) y
      have hAb0 : 0 ≤ ck ω b (directedNeighbor ω z Axis.horizontal) y := ck_nonneg ω hb0.le _ y
      have hBb0 : 0 ≤ ck ω b (directedNeighbor ω z Axis.vertical) y := ck_nonneg ω hb0.le _ y
      have hCb0 : 0 ≤ ck ω b z y := ck_nonneg ω hb0.le z y
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> nlinarith [hA, hB, hC, h0, h1, hA0, hB0, hAb0, hBb0, hCb0])
    ⟨ht, htb⟩ (summable_colSq ω ht.le y) ⟨ht, htb⟩
  exact hderiv.congr_deriv (tsum_ode_eq ω ht.le y)

theorem nash_energy_bound (ω : Environment) {s : ℝ} (hs : 0 ≤ s) (y : Site) :
    2 * (∑' z, ck ω s z y ^ 2) ^ 2 ≤ energy fun z => ck ω s z y := by
  have h := nash (fun z => ck ω s z y) (fun z => ck_nonneg ω hs z y) (summable_ck_col ω hs y)
  rw [tsum_ck_col ω hs y] at h
  nlinarith [h]

set_option maxHeartbeats 1000000 in
theorem colSq_le (ω : Environment) {t : ℝ} (ht : 0 ≤ t) (y : Site) :
    (∑' z, ck ω t z y ^ 2) ≤ 1 / (1 + 2 * t) := by
  rcases eq_or_lt_of_le ht with h0 | hpos
  · rw [← h0]
    have hz : ∀ z : Site, ck ω 0 z y ^ 2 = if z = y then (1:ℝ) else 0 := by
      intro z
      rw [ck_zero_time]
      by_cases h : z = y <;> simp [h]
    rw [tsum_congr hz, tsum_ite_eq y (fun _ => (1:ℝ))]
    norm_num
  · have hmono : MonotoneOn (fun r : ℝ => (∑' z, ck ω r z y ^ 2)⁻¹ - 2 * r) (Set.Ioi 0) := by
      have hd : ∀ r ∈ Set.Ioi (0:ℝ),
          HasDerivAt (fun q : ℝ => (∑' z, ck ω q z y ^ 2)⁻¹ - 2 * q)
            (energy (fun z => ck ω r z y) / (∑' z, ck ω r z y ^ 2) ^ 2 - 2) r := by
        intro r hr
        have hr0 : (0:ℝ) < r := hr
        have h1 := (hasDerivAt_colL2 ω hr0 y).inv (ne_of_gt (colSq_pos ω hr0.le y))
        have h2 : HasDerivAt (fun q : ℝ => 2 * q) 2 r := by
          simpa using (hasDerivAt_id r).const_mul (2:ℝ)
        refine (h1.sub h2).congr_deriv ?_
        field_simp
      refine monotoneOn_of_deriv_nonneg (convex_Ioi 0) ?_ ?_ ?_
      · exact fun r hr => (hd r hr).continuousAt.continuousWithinAt
      · intro r hr
        rw [interior_Ioi] at hr
        exact (hd r hr).differentiableAt.differentiableWithinAt
      · intro r hr
        rw [interior_Ioi] at hr
        rw [(hd r hr).deriv]
        have hr0 : (0:ℝ) < r := hr
        have hp := colSq_pos ω hr0.le y
        have hsq : (0:ℝ) < (∑' z, ck ω r z y ^ 2) ^ 2 := by positivity
        rw [sub_nonneg, le_div_iff₀ hsq]
        nlinarith [nash_energy_bound ω hr0.le y]
    have key : ∀ s : ℝ, 0 < s → s ≤ t → 1 + 2 * (t - s) ≤ (∑' z, ck ω t z y ^ 2)⁻¹ := by
      intro s hs hst
      have h1 := hmono (Set.mem_Ioi.2 hs) (Set.mem_Ioi.2 hpos) hst
      have hp := colSq_pos ω hs.le y
      have hl := colSq_le_one ω hs.le y
      have h2 : (1:ℝ) ≤ (∑' z, ck ω s z y ^ 2)⁻¹ := by
        nlinarith [mul_inv_cancel₀ (ne_of_gt hp), inv_pos.2 hp]
      simp only at h1
      linarith
    have hfin : 1 + 2 * t ≤ (∑' z, ck ω t z y ^ 2)⁻¹ := by
      by_contra hcon
      push_neg at hcon
      have hd0 : 0 < (1 + 2 * t - (∑' z, ck ω t z y ^ 2)⁻¹) / 4 := by linarith
      have hs : 0 < min ((1 + 2 * t - (∑' z, ck ω t z y ^ 2)⁻¹) / 4) t := lt_min hd0 hpos
      have hst : min ((1 + 2 * t - (∑' z, ck ω t z y ^ 2)⁻¹) / 4) t ≤ t := min_le_right _ _
      have hk := key _ hs hst
      have hmin : min ((1 + 2 * t - (∑' z, ck ω t z y ^ 2)⁻¹) / 4) t
          ≤ (1 + 2 * t - (∑' z, ck ω t z y ^ 2)⁻¹) / 4 := min_le_left _ _
      linarith
    have hp := colSq_pos ω ht y
    rw [le_div_iff₀ (show (0:ℝ) < 1 + 2 * t by linarith)]
    nlinarith [hfin, hp, mul_inv_cancel₀ (ne_of_gt hp)]
