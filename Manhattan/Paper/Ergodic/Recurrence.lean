import Manhattan.Paper.Ergodic.Alternating
import Manhattan.Model.MainTheorem

/-!
# Recurrence of the alternating environment

The remark of the manuscript closes by saying that every realization of the law
is a translate of the alternating environment, which is recurrent, and that the
recurrence is seen by halving both coordinates at even times: the resulting
process is the simple random walk on `ℤ²`.

This file proves that reduction.  Writing a site reached at an even time as
`(2a+γ, 2b+γ)` with `γ ∈ {0,1}` (`sitePos`), the theorem `two_step` shows that
two steps of the walk move the block `(a,b)` by one of the four unit vectors and
that the new `γ` is read off from that unit vector alone.  Counting words then
gives `two_mul_pathCount`: twice the number of `2(n+1)`-letter words returning
to the origin is the number of `(n+1)`-step simple-random-walk loops.  The
factor two is the constraint that the last block step be positive, and it is
removed by the reflection `S ↦ -S` in `blockReturn_add_neg`.

The only input left unproved is `SimpleRandomWalkRecurrent`, that the
two-dimensional simple random walk has a divergent Green series.  That is
Pólya's theorem, which Mathlib does not have.

Paper: the remark before `\begin{problem}[Which orientations are transient]`,
and the alternating environment of Section 1.
-/

namespace Manhattan.Paper.Ergodic

open scoped ENNReal NNReal

/-! ### One step of the alternating walk -/

/-- The alternating environment: `U = V = +1`. -/
def altBase : Environment := altEnv (.positive, .positive)

theorem step_horizontal (x y : ℤ) :
    directedNeighbor altBase (x, y) .horizontal = (x + negOne y, y) := by
  have hsign : (altBase (lineAt (x, y) .horizontal)).sign = negOne y := by
    show (parityShift Orientation.positive y).sign = negOne y
    rw [sign_parityShift]
    simp [Orientation.sign]
  simp [directedNeighbor, hsign, basisStep]

theorem step_vertical (x y : ℤ) :
    directedNeighbor altBase (x, y) .vertical = (x, y + negOne x) := by
  have hsign : (altBase (lineAt (x, y) .vertical)).sign = negOne x := by
    show (parityShift Orientation.positive x).sign = negOne x
    rw [sign_parityShift]
    simp [Orientation.sign]
  simp [directedNeighbor, hsign, basisStep]

/-! ### The four steps of the simple random walk -/

/-- The four unit steps of the two-dimensional simple random walk. -/
inductive Step
  | east | north | west | south
  deriving DecidableEq, Fintype, Inhabited

/-- The displacement of a step. -/
def Step.vec : Step → ℤ × ℤ
  | .east => (1, 0)
  | .north => (0, 1)
  | .west => (-1, 0)
  | .south => (0, -1)

/-- The reversed step. -/
def Step.neg : Step → Step
  | .east => .west
  | .north => .south
  | .west => .east
  | .south => .north

/-- The corner of the block occupied after a block step: `true` for the two
negative steps. -/
def Step.corner : Step → Bool
  | .east => false
  | .north => false
  | .west => true
  | .south => true

@[simp] theorem Step.neg_neg (s : Step) : s.neg.neg = s := by cases s <;> rfl

@[simp] theorem Step.vec_neg (s : Step) : s.neg.vec = -s.vec := by
  cases s <;> simp [Step.vec, Step.neg]

@[simp] theorem Step.corner_neg (s : Step) : s.neg.corner = !s.corner := by
  cases s <;> rfl

theorem sum_axis {M : Type*} [AddCommMonoid M] (g : Axis → M) :
    ∑ i : Axis, g i = g .horizontal + g .vertical := by
  rw [show (Finset.univ : Finset Axis) = {Axis.horizontal, Axis.vertical} by decide,
    Finset.sum_pair (by decide)]

theorem sum_step {M : Type*} [AddCommMonoid M] (f : Step → M) :
    ∑ s : Step, f s = f .east + f .north + f .west + f .south := by
  rw [show (Finset.univ : Finset Step) = {Step.east, Step.north, Step.west, Step.south} by
      decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  abel

theorem sum_step_neg {M : Type*} [AddCommMonoid M] (f : Step → M) :
    ∑ s : Step, f s.neg = ∑ s : Step, f s :=
  Fintype.sum_equiv (Function.Involutive.toPerm Step.neg Step.neg_neg)
    (fun s => f s.neg) f fun _ => rfl

/-! ### Blocks -/

/-- The offset of a corner. -/
def cornerVal : Bool → ℤ
  | false => 0
  | true => 1

/-- The site of the block `S` at corner `c`.  Every site reached at an even time
is of this shape. -/
def sitePos (S : ℤ × ℤ) (c : Bool) : Site :=
  (2 * S.1 + cornerVal c, 2 * S.2 + cornerVal c)

theorem sitePos_zero : sitePos 0 false = 0 := by
  simp [sitePos, cornerVal]

theorem sitePos_eq_zero_iff (S : ℤ × ℤ) (c : Bool) :
    sitePos S c = 0 ↔ S = 0 ∧ c = false := by
  obtain ⟨a, b⟩ := S
  cases c <;> simp [sitePos, cornerVal, Prod.ext_iff]
  omega

/-- The paper's coarse-graining: halve each coordinate and round down.  On `ℤ`
the quotient `/` rounds towards `-∞`. -/
def halve (z : Site) : ℤ × ℤ := (z.1 / 2, z.2 / 2)

/-- `sitePos` is a section of the paper's map: halving both coordinates of
`sitePos S c` and rounding down returns the block `S`. -/
theorem halve_sitePos (S : ℤ × ℤ) (c : Bool) : halve (sitePos S c) = S := by
  obtain ⟨a, b⟩ := S
  cases c
  · simp only [halve, sitePos, cornerVal, Prod.mk.injEq]
    omega
  · simp only [halve, sitePos, cornerVal, Prod.mk.injEq]
    omega

/-- The block step taken by the pair `(i,j)` of axis choices out of corner `c`. -/
def blockStep : Bool → Axis → Axis → Step
  | false, .horizontal, .horizontal => .east
  | false, .horizontal, .vertical => .south
  | false, .vertical, .horizontal => .west
  | false, .vertical, .vertical => .north
  | true, .horizontal, .horizontal => .west
  | true, .horizontal, .vertical => .north
  | true, .vertical, .horizontal => .east
  | true, .vertical, .vertical => .south

/-- Halving the coordinates at even times: two steps of the alternating walk
move the block by one simple-random-walk step, and the corner reached is a
function of that step alone. -/
theorem two_step (S : ℤ × ℤ) (c : Bool) (i j : Axis) :
    directedNeighbor altBase (directedNeighbor altBase (sitePos S c) i) j =
      sitePos (S + (blockStep c i j).vec) (blockStep c i j).corner := by
  obtain ⟨a, b⟩ := S
  cases c <;> cases i <;> cases j <;>
    simp only [sitePos, cornerVal, blockStep, Step.vec, Step.corner, step_horizontal,
      step_vertical, Prod.mk_add_mk, Prod.mk.injEq, negOne] <;>
    omega

/-- The manuscript's sentence, verbatim: at an even time the position with each
coordinate halved and rounded down moves, over the next two steps, by one step
of the simple random walk. -/
theorem halve_two_step (S : ℤ × ℤ) (c : Bool) (i j : Axis) :
    halve (directedNeighbor altBase (directedNeighbor altBase (sitePos S c) i) j) =
      halve (sitePos S c) + (blockStep c i j).vec := by
  rw [two_step, halve_sitePos, halve_sitePos]

/-- For each corner, the four pairs of axis choices give the four steps. -/
theorem sum_blockStep {M : Type*} [AddCommMonoid M] (c : Bool) (f : Step → M) :
    ∑ i : Axis, ∑ j : Axis, f (blockStep c i j) = ∑ s : Step, f s := by
  cases c
  · rw [sum_axis, sum_axis, sum_axis, sum_step]
    simp only [blockStep]
    abel
  · rw [sum_axis, sum_axis, sum_axis, sum_step]
    simp only [blockStep]
    abel

/-! ### Counting words -/

/-- The number of `n`-letter words steering the walk from `z` to `z'`. -/
def pathCount (ω : Environment) (n : ℕ) (z z' : Site) : ℕ :=
  ∑ path : Fin n → Axis, if followPath ω z (List.ofFn path) = z' then 1 else 0

theorem pathCount_zero (ω : Environment) (z z' : Site) :
    pathCount ω 0 z z' = if z = z' then 1 else 0 := by
  simp [pathCount]

theorem pathCount_succ (ω : Environment) (n : ℕ) (z z' : Site) :
    pathCount ω (n + 1) z z' = ∑ i : Axis, pathCount ω n (directedNeighbor ω z i) z' := by
  have hsplit :
      ∑ path : Fin (n + 1) → Axis, (if followPath ω z (List.ofFn path) = z' then 1 else 0) =
        ∑ p : Axis × (Fin n → Axis),
          (if followPath ω z (List.ofFn (Fin.cons p.1 p.2)) = z' then 1 else 0) :=
    (Fintype.sum_equiv (Fin.consEquiv fun _ : Fin (n + 1) => Axis)
      (fun p => if followPath ω z (List.ofFn (Fin.cons p.1 p.2)) = z' then 1 else 0)
      (fun path => if followPath ω z (List.ofFn path) = z' then 1 else 0) fun _ => rfl).symm
  rw [pathCount, hsplit, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pathCount]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [List.ofFn_succ]
  simp

/-- The number of `n`-step simple-random-walk paths carrying `T` to the origin. -/
def srwCount (n : ℕ) (T : ℤ × ℤ) : ℕ :=
  ∑ e : Fin n → Step, if T + ∑ k, (e k).vec = 0 then 1 else 0

theorem srwCount_zero (T : ℤ × ℤ) : srwCount 0 T = if T = 0 then 1 else 0 := by
  simp [srwCount]

theorem srwCount_succ (n : ℕ) (T : ℤ × ℤ) :
    srwCount (n + 1) T = ∑ s : Step, srwCount n (T + s.vec) := by
  have hsplit :
      ∑ e : Fin (n + 1) → Step, (if T + ∑ k, (e k).vec = 0 then 1 else 0) =
        ∑ p : Step × (Fin n → Step),
          (if T + ∑ k, ((Fin.cons p.1 p.2 : Fin (n + 1) → Step) k).vec = 0 then 1 else 0) :=
    (Fintype.sum_equiv (Fin.consEquiv fun _ : Fin (n + 1) => Step)
      (fun p => if T + ∑ k, ((Fin.cons p.1 p.2 : Fin (n + 1) → Step) k).vec = 0 then 1 else 0)
      (fun e => if T + ∑ k, (e k).vec = 0 then 1 else 0) fun _ => rfl).symm
  rw [srwCount, hsplit, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [srwCount]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Fin.sum_univ_succ]
  simp [← add_assoc]

/-! ### The two-step recursion -/

/-- The number of `2n`-letter words carrying the block `S` at corner `c` to the
origin. -/
def blockCount (n : ℕ) (S : ℤ × ℤ) (c : Bool) : ℕ :=
  pathCount altBase (2 * n) (sitePos S c) 0

theorem blockCount_zero (S : ℤ × ℤ) (c : Bool) :
    blockCount 0 S c = if S = 0 ∧ c = false then 1 else 0 := by
  rw [blockCount, Nat.mul_zero, pathCount_zero]
  simp only [sitePos_eq_zero_iff]

theorem blockCount_zero_add (T : ℤ × ℤ) (c : Bool) :
    blockCount 0 T c + blockCount 0 (-T) (!c) = if T = 0 then 1 else 0 := by
  rw [blockCount_zero, blockCount_zero]
  cases c <;> by_cases h : T = 0 <;> simp [h]

/-- The two-step recursion: the block performs a simple random walk. -/
theorem blockCount_succ (n : ℕ) (S : ℤ × ℤ) (c : Bool) :
    blockCount (n + 1) S c = ∑ s : Step, blockCount n (S + s.vec) s.corner := by
  rw [blockCount, show 2 * (n + 1) = 2 * n + 1 + 1 by ring, pathCount_succ]
  have hinner : ∀ i : Axis,
      pathCount altBase (2 * n + 1) (directedNeighbor altBase (sitePos S c) i) 0 =
        ∑ j : Axis, blockCount n (S + (blockStep c i j).vec) (blockStep c i j).corner := by
    intro i
    rw [pathCount_succ]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [blockCount, two_step]
  simp only [hinner]
  exact sum_blockStep c fun s => blockCount n (S + s.vec) s.corner

/-- Past the first block step the count no longer depends on the corner. -/
def blockReturn (n : ℕ) (S : ℤ × ℤ) : ℕ := blockCount (n + 1) S false

theorem blockCount_succ_corner (n : ℕ) (S : ℤ × ℤ) (c : Bool) :
    blockCount (n + 1) S c = blockReturn n S := by
  rw [blockReturn, blockCount_succ, blockCount_succ]

theorem blockReturn_succ (n : ℕ) (S : ℤ × ℤ) :
    blockReturn (n + 1) S = ∑ s : Step, blockReturn n (S + s.vec) := by
  rw [blockReturn, blockCount_succ]
  exact Finset.sum_congr rfl fun s _ => blockCount_succ_corner n (S + s.vec) s.corner

/-- The reflection `S ↦ -S` removes the constraint that the last block step be
positive: the two counts add up to the plain simple-random-walk count. -/
theorem blockReturn_add_neg : ∀ (n : ℕ) (S : ℤ × ℤ),
    blockReturn n S + blockReturn n (-S) = srwCount (n + 1) S
  | 0, S => by
      rw [blockReturn, blockReturn, blockCount_succ, blockCount_succ, srwCount_succ,
        ← sum_step_neg fun s => blockCount 0 (-S + s.vec) s.corner, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [srwCount_zero, Step.vec_neg, Step.corner_neg,
        show -S + -s.vec = -(S + s.vec) by abel]
      exact blockCount_zero_add (S + s.vec) s.corner
  | n + 1, S => by
      rw [blockReturn_succ, blockReturn_succ, srwCount_succ,
        ← sum_step_neg fun s => blockReturn n (-S + s.vec), ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Step.vec_neg, show -S + -s.vec = -(S + s.vec) by abel]
      exact blockReturn_add_neg n (S + s.vec)

/-- Twice the number of returning words of even length `2(n+1)` is the number of
simple-random-walk loops of length `n+1`. -/
theorem two_mul_pathCount (n : ℕ) :
    2 * pathCount altBase (2 * (n + 1)) 0 0 = srwCount (n + 1) 0 := by
  have h := blockReturn_add_neg n 0
  rw [neg_zero, blockReturn, blockCount, sitePos_zero] at h
  omega

/-! ### From word counts to kernels -/

theorem nStepKernel_eq_pathCount (ω : Environment) (n : ℕ) (z z' : Site) :
    nStepKernel ω n z z' = (2 : ℝ≥0)⁻¹ ^ n * (pathCount ω n z z' : ℝ≥0) := by
  rw [nStepKernel, pathCount, Nat.cast_sum]
  congr 1
  exact Finset.sum_congr rfl fun path _ => by split <;> simp

/-- The return probability of the two-dimensional simple random walk. -/
noncomputable def srwKernel (n : ℕ) : ℝ≥0 := (4 : ℝ≥0)⁻¹ ^ n * (srwCount n 0 : ℝ≥0)

theorem srwKernel_zero : srwKernel 0 = 1 := by
  rw [srwKernel, srwCount_zero]
  simp

theorem two_mul_nStepKernel (n : ℕ) :
    2 * nStepKernel altBase (2 * (n + 1)) 0 0 = srwKernel (n + 1) := by
  rw [nStepKernel_eq_pathCount, srwKernel,
    show (2 : ℝ≥0)⁻¹ ^ (2 * (n + 1)) = (4 : ℝ≥0)⁻¹ ^ (n + 1) by
      rw [pow_mul]; norm_num,
    ← mul_assoc, mul_comm (2 : ℝ≥0), mul_assoc]
  congr 1
  rw [show ((2 : ℝ≥0) : ℝ≥0) = ((2 : ℕ) : ℝ≥0) by norm_num, ← Nat.cast_mul, two_mul_pathCount]

/-! ### Recurrence -/

/-- Pólya's theorem in two dimensions: the Green series of the simple random
walk on `ℤ²` diverges.  This is the single named input that is not proved here;
Mathlib has no recurrence theorem for random walks. -/
def SimpleRandomWalkRecurrent : Prop := ∑' n : ℕ, (srwKernel n : ℝ≥0∞) = ⊤

/-- The alternating environment is recurrent. -/
theorem discreteGreen_altBase_eq_top (h : SimpleRandomWalkRecurrent) :
    discreteGreen altBase 0 = ⊤ := by
  have h' : ∑' n : ℕ, (srwKernel n : ℝ≥0∞) = ⊤ := h
  have htail : ∑' m : ℕ, (srwKernel (m + 1) : ℝ≥0∞) = ⊤ := by
    rw [tsum_eq_zero_add' ENNReal.summable] at h'
    rcases ENNReal.add_eq_top.mp h' with h0 | h1
    · exact absurd h0 ENNReal.coe_ne_top
    · exact h1
  have hmul : 2 * ∑' m : ℕ, (nStepKernel altBase (2 * (m + 1)) 0 0 : ℝ≥0∞) = ⊤ := by
    rw [← ENNReal.tsum_mul_left, ← htail]
    refine tsum_congr fun m => ?_
    rw [← two_mul_nStepKernel m]
    push_cast
    ring
  have hsub : ∑' m : ℕ, (nStepKernel altBase (2 * (m + 1)) 0 0 : ℝ≥0∞) = ⊤ := by
    rcases ENNReal.mul_eq_top.mp hmul with ⟨_, h2⟩ | ⟨h2, _⟩
    · exact h2
    · exact absurd h2 (by norm_num)
  have hinj : Function.Injective fun m : ℕ => 2 * (m + 1) := by
    intro a b hab
    have hab' : 2 * (a + 1) = 2 * (b + 1) := hab
    omega
  refine top_le_iff.mp ?_
  rw [← hsub, discreteGreen]
  exact ENNReal.tsum_comp_le_tsum_of_injective hinj _

/-! ### The other three environments -/

/-- Reflecting the axes according to the signs `(U,V)`. -/
def reflectSite (uv : Orientation × Orientation) (z : Site) : Site :=
  (uv.1.sign * z.1, uv.2.sign * z.2)

theorem reflectSite_zero (uv : Orientation × Orientation) : reflectSite uv 0 = 0 := by
  simp [reflectSite]

theorem reflectSite_eq_zero_iff (uv : Orientation × Orientation) (z : Site) :
    reflectSite uv z = 0 ↔ z = 0 := by
  obtain ⟨u, v⟩ := uv
  obtain ⟨p, q⟩ := z
  cases u <;> cases v <;> simp [reflectSite, Orientation.sign, Prod.ext_iff]

theorem directedNeighbor_reflect (uv : Orientation × Orientation) (z : Site) (i : Axis) :
    directedNeighbor (altEnv uv) (reflectSite uv z) i =
      reflectSite uv (directedNeighbor altBase z i) := by
  obtain ⟨p, q⟩ := z
  cases i
  · have hsign : (altEnv uv (lineAt (reflectSite uv (p, q)) Axis.horizontal)).sign =
        negOne q * uv.1.sign := by
      show (parityShift uv.1 (uv.2.sign * q)).sign = negOne q * uv.1.sign
      rw [parityShift_sign_mul, sign_parityShift]
    have hL : directedNeighbor (altEnv uv) (reflectSite uv (p, q)) Axis.horizontal =
        (uv.1.sign * p + negOne q * uv.1.sign, uv.2.sign * q) := by
      simp only [directedNeighbor, hsign, basisStep]
      simp [reflectSite]
    rw [hL, step_horizontal]
    simp only [reflectSite, Prod.mk.injEq]
    exact ⟨by ring, trivial⟩
  · have hsign : (altEnv uv (lineAt (reflectSite uv (p, q)) Axis.vertical)).sign =
        negOne p * uv.2.sign := by
      show (parityShift uv.2 (uv.1.sign * p)).sign = negOne p * uv.2.sign
      rw [parityShift_sign_mul, sign_parityShift]
    have hL : directedNeighbor (altEnv uv) (reflectSite uv (p, q)) Axis.vertical =
        (uv.1.sign * p, uv.2.sign * q + negOne p * uv.2.sign) := by
      simp only [directedNeighbor, hsign, basisStep]
      simp [reflectSite]
    rw [hL, step_vertical]
    simp only [reflectSite, Prod.mk.injEq]
    exact ⟨trivial, by ring⟩

theorem followPath_reflect (uv : Orientation × Orientation) (z : Site) (path : List Axis) :
    followPath (altEnv uv) (reflectSite uv z) path =
      reflectSite uv (followPath altBase z path) := by
  induction path generalizing z with
  | nil => rfl
  | cons i path ih => rw [followPath_cons, followPath_cons, directedNeighbor_reflect, ih]

theorem pathCount_altEnv (uv : Orientation × Orientation) (n : ℕ) :
    pathCount (altEnv uv) n 0 0 = pathCount altBase n 0 0 := by
  refine Finset.sum_congr rfl fun path _ => ?_
  rw [show (0 : Site) = reflectSite uv 0 from (reflectSite_zero uv).symm]
  rw [followPath_reflect]
  simp only [reflectSite_eq_zero_iff, reflectSite_zero]

theorem nStepKernel_altEnv (uv : Orientation × Orientation) (n : ℕ) :
    nStepKernel (altEnv uv) n 0 0 = nStepKernel altBase n 0 0 := by
  rw [nStepKernel_eq_pathCount, nStepKernel_eq_pathCount, pathCount_altEnv]

/-- Every realization of the law is recurrent. -/
theorem discreteGreen_altEnv_eq_top (h : SimpleRandomWalkRecurrent)
    (uv : Orientation × Orientation) : discreteGreen (altEnv uv) 0 = ⊤ := by
  rw [discreteGreen, ← discreteGreen_altBase_eq_top h, discreteGreen]
  exact tsum_congr fun n => by rw [nStepKernel_altEnv]

end Manhattan.Paper.Ergodic
