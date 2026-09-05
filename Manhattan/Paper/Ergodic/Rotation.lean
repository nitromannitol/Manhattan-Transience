/-
The 45 degree rotation that splits the two dimensional walk.

The map `(x, y) ↦ (x + y, x - y)` carries the four steps `(±1, 0), (0, ±1)` to
the four diagonal steps `(±1, ±1)`, whose two coordinates move independently.
So a two dimensional walk word is exactly a pair of one dimensional sign words,
and it returns to the origin exactly when both of them do. That independence is
the whole reason the planar return count is a square.
-/
import Manhattan.Paper.Ergodic.Recurrence

namespace Manhattan.Paper.Ergodic

open Finset

/-- The pair of signs a step carries in rotated coordinates. -/
def Step.sgn : Step → Bool × Bool
  | .east => (true, true)
  | .north => (true, false)
  | .west => (false, false)
  | .south => (false, true)

/-- The step with a given pair of rotated signs. -/
def Step.ofSgn : Bool × Bool → Step
  | (true, true) => .east
  | (true, false) => .north
  | (false, false) => .west
  | (false, true) => .south

/-- A step is exactly a pair of signs. -/
def stepEquivSigns : Step ≃ Bool × Bool where
  toFun := Step.sgn
  invFun := Step.ofSgn
  left_inv s := by cases s <;> rfl
  right_inv := by rintro ⟨a, b⟩; cases a <;> cases b <;> rfl

/-- `true` counts `+1`, `false` counts `-1`. -/
def sgnVal (b : Bool) : ℤ := if b then 1 else -1

@[simp] theorem sgnVal_true : sgnVal true = 1 := rfl
@[simp] theorem sgnVal_false : sgnVal false = -1 := rfl

/-- The rotation sends a step's displacement to its pair of signs. -/
theorem rot_vec (s : Step) :
    (s.vec.1 + s.vec.2 = sgnVal s.sgn.1) ∧ (s.vec.1 - s.vec.2 = sgnVal s.sgn.2) := by
  cases s <;> exact ⟨by decide, by decide⟩

/-- A displacement vanishes exactly when both rotated coordinates do. The
rotation is injective because its determinant is `-2 ≠ 0`, and `ℤ` is
torsion-free, which is what the doubling below uses. -/
theorem eq_zero_iff_rot (A B : ℤ) : (A, B) = (0, 0) ↔ A + B = 0 ∧ A - B = 0 := by
  constructor
  · rintro h
    have h1 : A = 0 := congrArg Prod.fst h
    have h2 : B = 0 := congrArg Prod.snd h
    subst h1; subst h2; exact ⟨by ring, by ring⟩
  · rintro ⟨h1, h2⟩
    have hA : (2 : ℤ) * A = 0 := by linarith
    have hB : (2 : ℤ) * B = 0 := by linarith
    have hA' : A = 0 := by linarith
    have hB' : B = 0 := by linarith
    subst hA'; subst hB'; rfl

end Manhattan.Paper.Ergodic
