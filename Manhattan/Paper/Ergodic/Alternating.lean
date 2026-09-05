import Manhattan.Model.Kernel
import Mathlib.Algebra.Ring.NegOnePow

/-!
# The four alternating environments

The remark of `manuscript.tex` preceding `\begin{problem}\label{prob:which}`
exhibits a law that is stationary and ergodic for the full `ℤ²` translation
action, has fair one-point marginals, and is nevertheless recurrent. Its
environments are

```
  ω((x,y),1) = U·(-1)^y, ω((x,y),2) = V·(-1)^x
```

for two signs `U, V`. This file builds the four environments `altEnv (U,V)`,
records that the paper's raw field really is constant along lines (part (i) of
the remark), and computes the translation action on the family.

Paper: the remark before `\begin{problem}[Which orientations are transient]`.
-/

namespace Manhattan.Paper.Ergodic

open Manhattan

/-! ### Signs -/

/-- The opposite orientation. -/
def flipOrientation : Orientation → Orientation
  | .negative => .positive
  | .positive => .negative

@[simp] theorem flipOrientation_flipOrientation (o : Orientation) :
    flipOrientation (flipOrientation o) = o := by cases o <;> rfl

@[simp] theorem sign_flipOrientation (o : Orientation) :
    (flipOrientation o).sign = -o.sign := by cases o <;> rfl

theorem flipOrientation_ne (o : Orientation) : flipOrientation o ≠ o := by
  cases o <;> decide

/-- `(-1)^k`, written so that `omega` can use it. -/
def negOne (k : ℤ) : ℤ := 1 - 2 * (k % 2)

/-- `negOne` is the integer `(-1)^k` of the paper. -/
theorem negOne_eq_negOnePow (k : ℤ) : negOne k = (Int.negOnePow k : ℤ) := by
  rcases Int.even_or_odd k with h | h
  · rw [Int.negOnePow_even k h]
    obtain ⟨m, rfl⟩ := h
    simp only [negOne, Units.val_one]
    omega
  · rw [Int.negOnePow_odd k h]
    obtain ⟨m, rfl⟩ := h
    simp only [negOne, Units.val_neg, Units.val_one]
    omega

@[simp] theorem negOne_two_mul (k : ℤ) : negOne (2 * k) = 1 := by
  simp only [negOne]; omega

@[simp] theorem negOne_two_mul_add_one (k : ℤ) : negOne (2 * k + 1) = -1 := by
  simp only [negOne]; omega

theorem negOne_neg (k : ℤ) : negOne (-k) = negOne k := by
  simp only [negOne]; omega

/-- The orientation `o` multiplied by the sign `(-1)^k`. -/
def parityShift (o : Orientation) (k : ℤ) : Orientation :=
  if k % 2 = 0 then o else flipOrientation o

@[simp] theorem parityShift_zero (o : Orientation) : parityShift o 0 = o := by
  simp [parityShift]

@[simp] theorem parityShift_one (o : Orientation) : parityShift o 1 = flipOrientation o := by
  simp [parityShift]

theorem parityShift_of_even (o : Orientation) {k m : ℤ} (h : k = 2 * m) :
    parityShift o k = o := by
  have hk : k % 2 = 0 := by omega
  simp [parityShift, hk]

theorem parityShift_of_odd (o : Orientation) {k m : ℤ} (h : k = 2 * m + 1) :
    parityShift o k = flipOrientation o := by
  have : ¬ (k % 2 = 0) := by omega
  simp [parityShift, this]

theorem parityShift_add (o : Orientation) (k m : ℤ) :
    parityShift o (k + m) = parityShift (parityShift o k) m := by
  by_cases hk : k % 2 = 0 <;> by_cases hm : m % 2 = 0
  · have h : (k + m) % 2 = 0 := by omega
    simp [parityShift, h, hk, hm]
  · have h : ¬ ((k + m) % 2 = 0) := by omega
    simp [parityShift, h, hk, hm]
  · have h : ¬ ((k + m) % 2 = 0) := by omega
    simp [parityShift, h, hk, hm]
  · have h : (k + m) % 2 = 0 := by omega
    simp [parityShift, h, hk, hm]

@[simp] theorem parityShift_parityShift (o : Orientation) (k : ℤ) :
    parityShift (parityShift o k) k = o := by
  by_cases hk : k % 2 = 0 <;> simp [parityShift, hk]

theorem parityShift_neg (o : Orientation) (k : ℤ) :
    parityShift o (-k) = parityShift o k := by
  by_cases hk : k % 2 = 0 <;> simp [parityShift, hk]

theorem parityShift_sign_mul (o o' : Orientation) (k : ℤ) :
    parityShift o (o'.sign * k) = parityShift o k := by
  cases o' <;> simp [Orientation.sign, parityShift_neg]

theorem sign_parityShift (o : Orientation) (k : ℤ) :
    (parityShift o k).sign = negOne k * o.sign := by
  by_cases hk : k % 2 = 0
  · have h : negOne k = 1 := by simp only [negOne]; omega
    simp [parityShift, hk, h]
  · have h : negOne k = -1 := by simp only [negOne]; omega
    simp [parityShift, hk, h]

/-! ### The environments -/

/-- The environment with horizontal signs `U·(-1)^k` and vertical signs `V·(-1)^k`. -/
def altEnv (uv : Orientation × Orientation) : Environment := fun l =>
  match l with
  | (.horizontal, k) => parityShift uv.1 k
  | (.vertical, k) => parityShift uv.2 k

@[simp] theorem altEnv_horizontal (uv : Orientation × Orientation) (k : ℤ) :
    altEnv uv (.horizontal, k) = parityShift uv.1 k := rfl

@[simp] theorem altEnv_vertical (uv : Orientation × Orientation) (k : ℤ) :
    altEnv uv (.vertical, k) = parityShift uv.2 k := rfl

/-- The paper's raw orientation field `ω(z,i)`, before the redundant site index
is discarded. -/
def rawOrientation (uv : Orientation × Orientation) (z : Site) : Axis → ℤ
  | .horizontal => (Int.negOnePow z.2 : ℤ) * uv.1.sign
  | .vertical => (Int.negOnePow z.1 : ℤ) * uv.2.sign

/-- Part (i) of the remark: the raw field is the sign of a genuine environment,
that is, it is constant along each line. -/
theorem rawOrientation_eq_sign (uv : Orientation × Orientation) (z : Site) (i : Axis) :
    rawOrientation uv z i = (altEnv uv (lineAt z i)).sign := by
  cases i <;>
    simp [rawOrientation, lineAt, transverseCoordinate, sign_parityShift,
      negOne_eq_negOnePow]

/-- Part (i), explicitly: the horizontal orientation does not depend on the
site's own horizontal coordinate. -/
theorem rawOrientation_horizontal_indep (uv : Orientation × Orientation) (x x' y : ℤ) :
    rawOrientation uv (x, y) .horizontal = rawOrientation uv (x', y) .horizontal := rfl

/-- Part (i), explicitly: the vertical orientation does not depend on the site's
own vertical coordinate. -/
theorem rawOrientation_vertical_indep (uv : Orientation × Orientation) (x y y' : ℤ) :
    rawOrientation uv (x, y) .vertical = rawOrientation uv (x, y') .vertical := rfl

/-- The paper's display for the horizontal orientations. -/
theorem altEnv_sign_horizontal (uv : Orientation × Orientation) (x y : ℤ) :
    (altEnv uv (lineAt (x, y) .horizontal)).sign = (Int.negOnePow y : ℤ) * uv.1.sign := by
  simp [lineAt, transverseCoordinate, sign_parityShift, negOne_eq_negOnePow]

/-- The paper's display for the vertical orientations. -/
theorem altEnv_sign_vertical (uv : Orientation × Orientation) (x y : ℤ) :
    (altEnv uv (lineAt (x, y) .vertical)).sign = (Int.negOnePow x : ℤ) * uv.2.sign := by
  simp [lineAt, transverseCoordinate, sign_parityShift, negOne_eq_negOnePow]

/-- The family has four distinct members. -/
theorem altEnv_injective : Function.Injective altEnv := by
  rintro ⟨u, v⟩ ⟨u', v'⟩ h
  have h1 : parityShift u 0 = parityShift u' 0 := congrArg (fun ω => ω (.horizontal, 0)) h
  have h2 : parityShift v 0 = parityShift v' 0 := congrArg (fun ω => ω (.vertical, 0)) h
  simp only [parityShift_zero] at h1 h2
  simp [h1, h2]

/-- Witness: the sign at height `0`. -/
theorem altEnv_pp_zero : altEnv (.positive, .positive) (.horizontal, 0) = .positive := rfl

/-- Witness: the environments really do alternate along a line. -/
theorem altEnv_pp_one : altEnv (.positive, .positive) (.horizontal, 1) = .negative := rfl

/-- Witness: two members of the family differ. -/
theorem altEnv_pp_ne_np : altEnv (.positive, .positive) ≠ altEnv (.negative, .positive) := by
  intro h
  have hval := congrArg (fun ω => ω (.horizontal, 0)) h
  simp at hval

/-! ### The translation action -/

/-- Translating by `x` multiplies `U` by `(-1)^{x₂}` and `V` by `(-1)^{x₁}`. -/
def shiftSigns (x : Site) (uv : Orientation × Orientation) : Orientation × Orientation :=
  (parityShift uv.1 x.2, parityShift uv.2 x.1)

/-- The family is invariant under the translation action, with the explicit
sign rule `shiftSigns`. -/
theorem translateEnvironment_altEnv (x : Site) (uv : Orientation × Orientation) :
    translateEnvironment x (altEnv uv) = altEnv (shiftSigns x uv) := by
  funext l
  obtain ⟨i, k⟩ := l
  cases i <;>
    simp [translateEnvironment, lineTranslation, transverseCoordinate, shiftSigns,
      add_comm k, parityShift_add]

/-- Translation by `(1,0)` flips `V` and fixes `U`, as the paper says. -/
theorem translate_one_zero (uv : Orientation × Orientation) :
    translateEnvironment (1, 0) (altEnv uv) = altEnv (uv.1, flipOrientation uv.2) := by
  rw [translateEnvironment_altEnv]
  simp [shiftSigns]

/-- Translation by `(0,1)` flips `U` and fixes `V`, as the paper says. -/
theorem translate_zero_one (uv : Orientation × Orientation) :
    translateEnvironment (0, 1) (altEnv uv) = altEnv (flipOrientation uv.1, uv.2) := by
  rw [translateEnvironment_altEnv]
  simp [shiftSigns]

/-- Translation by `(1,1)` flips both signs. -/
theorem translate_one_one (uv : Orientation × Orientation) :
    translateEnvironment (1, 1) (altEnv uv) =
      altEnv (flipOrientation uv.1, flipOrientation uv.2) := by
  rw [translateEnvironment_altEnv]
  simp [shiftSigns]

/-- Every even translation fixes every member of the family: the law is not
ergodic for `2ℤ²`. -/
theorem translate_even (a b : ℤ) (uv : Orientation × Orientation) :
    translateEnvironment (2 * a, 2 * b) (altEnv uv) = altEnv uv := by
  rw [translateEnvironment_altEnv]
  simp [shiftSigns, parityShift_of_even _ (m := b) rfl, parityShift_of_even _ (m := a) rfl]

/-- The explicit translation carrying `uv` to `uv'`. -/
def transitionSite (uv uv' : Orientation × Orientation) : Site :=
  (if uv.2 = uv'.2 then 0 else 1, if uv.1 = uv'.1 then 0 else 1)

/-- The translation action is transitive on the four environments, with the
explicit group element `transitionSite`. -/
theorem translate_transitive (uv uv' : Orientation × Orientation) :
    translateEnvironment (transitionSite uv uv') (altEnv uv) = altEnv uv' := by
  rw [translateEnvironment_altEnv]
  obtain ⟨u, v⟩ := uv
  obtain ⟨u', v'⟩ := uv'
  cases u <;> cases v <;> cases u' <;> cases v' <;>
    simp [shiftSigns, transitionSite, flipOrientation]

/-- Every realization is a translate of the alternating environment
`altEnv (+,+)`. -/
theorem altEnv_eq_translate_base (uv : Orientation × Orientation) :
    altEnv uv =
      translateEnvironment (transitionSite (.positive, .positive) uv)
        (altEnv (.positive, .positive)) :=
  (translate_transitive _ _).symm

end Manhattan.Paper.Ergodic
