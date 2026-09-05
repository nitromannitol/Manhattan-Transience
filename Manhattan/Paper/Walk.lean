import Manhattan.Model.Kernel
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic

/-!
# The quenched discrete-time kernel as a doubly stochastic chain

The Manhattan jump chain moves along a fixed axis in the direction of the line
through the current site, so each single step is a *bijection* of `ℤ²`.  This
file records the consequences used by `prop:time` of `manuscript.tex`:

* `flipEnv`, the environment with every line reversed, inverts each step;
* the backward recursion `dk_succ` and the forward recursion `dk_succ_right`;
* both marginals of the `n`-step kernel are probability measures;
* the Chapman-Kolmogorov identity `dk_chapman`;
* the reversal identity `dk_flipEnv`, which turns a row of the kernel into a
  column of the kernel of the reversed environment.
-/

open scoped BigOperators

namespace Manhattan.Paper

/-! ### Reversing the environment -/

/-- The opposite orientation. -/
def flipOrientation : Orientation → Orientation
  | .negative => .positive
  | .positive => .negative

@[simp] theorem flipOrientation_flipOrientation (o : Orientation) :
    flipOrientation (flipOrientation o) = o := by cases o <;> rfl

@[simp] theorem sign_flipOrientation (o : Orientation) :
    (flipOrientation o).sign = -o.sign := by cases o <;> rfl

/-- The environment with every line orientation reversed. -/
def flipEnv (ω : Environment) : Environment := fun l => flipOrientation (ω l)

@[simp] theorem flipEnv_flipEnv (ω : Environment) : flipEnv (flipEnv ω) = ω := by
  funext l; simp [flipEnv]

theorem lineAt_directedNeighbor (ω : Environment) (z : Site) (i : Axis) :
    lineAt (directedNeighbor ω z i) i = lineAt z i := by
  obtain ⟨a, b⟩ := z
  cases i <;>
    simp [lineAt, transverseCoordinate, directedNeighbor, basisStep, Prod.smul_mk]

theorem directedNeighbor_flipEnv (ω : Environment) (z : Site) (i : Axis) :
    directedNeighbor (flipEnv ω) (directedNeighbor ω z i) i = z := by
  have hl : lineAt (directedNeighbor ω z i) i = lineAt z i := lineAt_directedNeighbor ω z i
  conv_lhs => rw [directedNeighbor, hl]
  simp only [flipEnv, sign_flipOrientation, neg_smul, directedNeighbor]
  abel

/-- One directed step, as a bijection of the lattice. -/
def stepEquiv (ω : Environment) (i : Axis) : Site ≃ Site where
  toFun z := directedNeighbor ω z i
  invFun z := directedNeighbor (flipEnv ω) z i
  left_inv z := directedNeighbor_flipEnv ω z i
  right_inv z := by
    have h := directedNeighbor_flipEnv (flipEnv ω) z i
    rwa [flipEnv_flipEnv] at h

@[simp] theorem stepEquiv_apply (ω : Environment) (i : Axis) (z : Site) :
    stepEquiv ω i z = directedNeighbor ω z i := rfl

@[simp] theorem stepEquiv_symm_apply (ω : Environment) (i : Axis) (z : Site) :
    (stepEquiv ω i).symm z = directedNeighbor (flipEnv ω) z i := rfl

/-- Following a fixed word of axes is a bijection of the lattice. -/
def followEquiv (ω : Environment) : List Axis → Site ≃ Site
  | [] => Equiv.refl Site
  | i :: l => (stepEquiv ω i).trans (followEquiv ω l)

theorem followEquiv_apply (ω : Environment) (l : List Axis) (z : Site) :
    followEquiv ω l z = followPath ω z l := by
  induction l generalizing z with
  | nil => rfl
  | cons i l ih => simpa [followEquiv, stepEquiv] using ih (directedNeighbor ω z i)

/-! ### The real-valued discrete kernel -/

/-- The quenched `n`-step transition kernel, as a real number. -/
noncomputable def dk (ω : Environment) (n : ℕ) (x y : Site) : ℝ := (nStepKernel ω n x y : ℝ)

theorem dk_nonneg (ω : Environment) (n : ℕ) (x y : Site) : 0 ≤ dk ω n x y :=
  (nStepKernel ω n x y).coe_nonneg

theorem dk_eq (ω : Environment) (n : ℕ) (x y : Site) :
    dk ω n x y = (2:ℝ)⁻¹ ^ n * ∑ p : Fin n → Axis,
      if followPath ω x (List.ofFn p) = y then (1:ℝ) else 0 := by
  simp only [dk, nStepKernel, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_inv, NNReal.coe_ofNat,
    NNReal.coe_sum, apply_ite NNReal.toReal, NNReal.coe_one, NNReal.coe_zero]

@[simp] theorem dk_zero (ω : Environment) (x y : Site) :
    dk ω 0 x y = if x = y then 1 else 0 := by
  simp only [dk, nStepKernel_zero, apply_ite NNReal.toReal, NNReal.coe_one, NNReal.coe_zero]

theorem sum_axis (F : Axis → ℝ) : ∑ i : Axis, F i = F Axis.horizontal + F Axis.vertical := by
  rw [show (Finset.univ : Finset Axis) = {Axis.horizontal, Axis.vertical} by decide]
  simp

/-- The backward recursion: conditioning on the first step. -/
theorem dk_succ (ω : Environment) (n : ℕ) (x y : Site) :
    dk ω (n + 1) x y =
      (2:ℝ)⁻¹ * (dk ω n (directedNeighbor ω x Axis.horizontal) y
        + dk ω n (directedNeighbor ω x Axis.vertical) y) := by
  have hsplit : (∑ p : Fin (n + 1) → Axis,
        if followPath ω x (List.ofFn p) = y then (1:ℝ) else 0)
      = ∑ i : Axis, ∑ q : Fin n → Axis,
        if followPath ω (directedNeighbor ω x i) (List.ofFn q) = y then (1:ℝ) else 0 := by
    have hprod : (∑ r : Axis × (Fin n → Axis),
          if followPath ω (directedNeighbor ω x r.1) (List.ofFn r.2) = y then (1:ℝ) else 0)
        = ∑ i : Axis, ∑ q : Fin n → Axis,
          if followPath ω (directedNeighbor ω x i) (List.ofFn q) = y then (1:ℝ) else 0 :=
      Fintype.sum_prod_type _
    rw [← hprod]
    refine (Fintype.sum_equiv (Fin.consEquiv fun _ : Fin (n + 1) => Axis) _ _ ?_).symm
    rintro ⟨a, q⟩
    simp
  rw [dk_eq, hsplit, sum_axis, dk_eq, dk_eq, pow_succ]
  ring

/-! ### Both marginals are probability measures -/

/-- Rows of the `n`-step kernel sum to one: the chain is stochastic. -/
theorem hasSum_dk_row (ω : Environment) (n : ℕ) (x : Site) :
    HasSum (fun y => dk ω n x y) 1 := by
  induction n generalizing x with
  | zero =>
      have h : (fun y => dk ω 0 x y) = fun y => if y = x then (1:ℝ) else 0 := by
        funext y
        rw [dk_zero]
        by_cases hxy : x = y
        · simp [hxy]
        · simp [hxy, Ne.symm hxy]
      rw [h]
      simpa using hasSum_ite_eq x (1:ℝ)
  | succ n ih =>
      have h := ((ih (directedNeighbor ω x Axis.horizontal)).add
        (ih (directedNeighbor ω x Axis.vertical))).mul_left (2:ℝ)⁻¹
      have he : (2:ℝ)⁻¹ * (1 + 1) = 1 := by norm_num
      rw [he] at h
      exact h.congr_fun fun y => dk_succ ω n x y

/-- Columns of the `n`-step kernel sum to one: the chain is doubly stochastic. -/
theorem hasSum_dk_col (ω : Environment) (n : ℕ) (y : Site) :
    HasSum (fun x => dk ω n x y) 1 := by
  induction n generalizing y with
  | zero =>
      have h : (fun x => dk ω 0 x y) = fun x => if x = y then (1:ℝ) else 0 := by
        funext x; rw [dk_zero]
      rw [h]
      simpa using hasSum_ite_eq y (1:ℝ)
  | succ n ih =>
      have h1 : HasSum (fun x => dk ω n (directedNeighbor ω x Axis.horizontal) y) 1 :=
        ((stepEquiv ω Axis.horizontal).hasSum_iff (f := fun w => dk ω n w y)).2 (ih y)
      have h2 : HasSum (fun x => dk ω n (directedNeighbor ω x Axis.vertical) y) 1 :=
        ((stepEquiv ω Axis.vertical).hasSum_iff (f := fun w => dk ω n w y)).2 (ih y)
      have h := (h1.add h2).mul_left (2:ℝ)⁻¹
      have he : (2:ℝ)⁻¹ * (1 + 1) = 1 := by norm_num
      rw [he] at h
      exact h.congr_fun fun x => dk_succ ω n x y

theorem summable_dk_row (ω : Environment) (n : ℕ) (x : Site) :
    Summable fun y => dk ω n x y := (hasSum_dk_row ω n x).summable

theorem summable_dk_col (ω : Environment) (n : ℕ) (y : Site) :
    Summable fun x => dk ω n x y := (hasSum_dk_col ω n y).summable

theorem tsum_dk_row (ω : Environment) (n : ℕ) (x : Site) : ∑' y, dk ω n x y = 1 :=
  (hasSum_dk_row ω n x).tsum_eq

theorem tsum_dk_col (ω : Environment) (n : ℕ) (y : Site) : ∑' x, dk ω n x y = 1 :=
  (hasSum_dk_col ω n y).tsum_eq

theorem dk_le_one (ω : Environment) (n : ℕ) (x y : Site) : dk ω n x y ≤ 1 := by
  have h := (summable_dk_row ω n x).le_tsum y (fun j _ => dk_nonneg ω n x j)
  rwa [tsum_dk_row] at h

/-! ### Chapman-Kolmogorov, the forward recursion, and reversal -/

theorem summable_dk_mul (ω : Environment) (m n : ℕ) (x y : Site) :
    Summable fun z => dk ω m x z * dk ω n z y := by
  refine Summable.of_nonneg_of_le (fun z => mul_nonneg (dk_nonneg _ _ _ _) (dk_nonneg _ _ _ _))
    (fun z => ?_) (summable_dk_row ω m x)
  calc dk ω m x z * dk ω n z y ≤ dk ω m x z * 1 :=
        mul_le_mul_of_nonneg_left (dk_le_one ω n z y) (dk_nonneg _ _ _ _)
    _ = dk ω m x z := mul_one _

theorem summable_dk_mul_ite (ω : Environment) (n : ℕ) (x y : Site) (i : Axis) :
    Summable fun z => dk ω n x z * (if directedNeighbor ω z i = y then (1:ℝ) else 0) := by
  refine Summable.of_nonneg_of_le (fun z => ?_) (fun z => ?_) (summable_dk_row ω n x)
  · refine mul_nonneg (dk_nonneg _ _ _ _) ?_
    split <;> norm_num
  · by_cases h : directedNeighbor ω z i = y
    · simp [h]
    · simp [h, dk_nonneg]

/-- The Chapman-Kolmogorov identity for the quenched discrete-time chain. -/
theorem dk_chapman (ω : Environment) (m n : ℕ) (x y : Site) :
    dk ω (m + n) x y = ∑' z, dk ω m x z * dk ω n z y := by
  induction m generalizing x with
  | zero =>
      simp only [Nat.zero_add]
      rw [tsum_eq_single x fun z hz => by rw [dk_zero]; simp [Ne.symm hz]]
      simp
  | succ m ih =>
      have hidx : m + 1 + n = m + n + 1 := by omega
      rw [hidx, dk_succ, ih, ih,
        ← Summable.tsum_add (summable_dk_mul ω m n _ y) (summable_dk_mul ω m n _ y),
        ← tsum_mul_left]
      exact tsum_congr fun z => by rw [dk_succ]; ring

/-- The forward recursion: conditioning on the last step. -/
theorem dk_succ_right (ω : Environment) (n : ℕ) (x y : Site) :
    dk ω (n + 1) x y =
      (2:ℝ)⁻¹ * (dk ω n x (directedNeighbor (flipEnv ω) y Axis.horizontal)
        + dk ω n x (directedNeighbor (flipEnv ω) y Axis.vertical)) := by
  have hone : ∀ z : Site, dk ω 1 z y
      = (2:ℝ)⁻¹ * ((if directedNeighbor ω z Axis.horizontal = y then (1:ℝ) else 0)
        + (if directedNeighbor ω z Axis.vertical = y then (1:ℝ) else 0)) := by
    intro z
    have h0 := dk_succ ω 0 z y
    simp only [Nat.zero_add, dk_zero] at h0
    exact h0
  have hsingle : ∀ i : Axis,
      (∑' z, dk ω n x z * (if directedNeighbor ω z i = y then (1:ℝ) else 0))
        = dk ω n x (directedNeighbor (flipEnv ω) y i) := by
    intro i
    rw [tsum_eq_single (directedNeighbor (flipEnv ω) y i) ?_]
    · have hy : directedNeighbor ω (directedNeighbor (flipEnv ω) y i) i = y := by
        simpa using (stepEquiv ω i).apply_symm_apply y
      rw [if_pos hy, mul_one]
    · intro z hz
      rw [if_neg, mul_zero]
      intro hcon
      apply hz
      have := (stepEquiv ω i).symm_apply_apply z
      simp only [stepEquiv_apply, stepEquiv_symm_apply] at this
      rw [← this, hcon]
  rw [dk_chapman ω n 1 x y]
  calc ∑' z, dk ω n x z * dk ω 1 z y
      = ∑' z, (2:ℝ)⁻¹ *
          (dk ω n x z * (if directedNeighbor ω z Axis.horizontal = y then (1:ℝ) else 0)
            + dk ω n x z * (if directedNeighbor ω z Axis.vertical = y then (1:ℝ) else 0)) := by
        exact tsum_congr fun z => by rw [hone z]; ring
    _ = (2:ℝ)⁻¹ *
          ((∑' z, dk ω n x z * (if directedNeighbor ω z Axis.horizontal = y then (1:ℝ) else 0))
            + ∑' z, dk ω n x z * (if directedNeighbor ω z Axis.vertical = y then (1:ℝ) else 0)) := by
        rw [tsum_mul_left, Summable.tsum_add (summable_dk_mul_ite ω n x y Axis.horizontal)
          (summable_dk_mul_ite ω n x y Axis.vertical)]
    _ = _ := by rw [hsingle, hsingle]

/-- Reversing the environment transposes the kernel. -/
theorem dk_flipEnv (ω : Environment) (n : ℕ) (x y : Site) :
    dk ω n x y = dk (flipEnv ω) n y x := by
  induction n generalizing x y with
  | zero =>
      rw [dk_zero, dk_zero]
      by_cases h : x = y
      · simp [h]
      · simp [h, Ne.symm h]
  | succ n ih =>
      rw [dk_succ, dk_succ_right (flipEnv ω) n y x, flipEnv_flipEnv, ih, ih]
