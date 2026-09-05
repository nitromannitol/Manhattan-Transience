import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Version 4: the two scalar minimizations

Two elementary real identities carry the whole optimization in the Version 4
argument.

* `scalarCompletion_*`: for `B > 0`, `sigma ≥ 0` and any real `w`,
  `⨅ v, (sigma v² + (w - sigma v)²/B) = w²/(B + sigma)`, attained at
  `v = w/(B + sigma)`. Applied pointwise in the frequencies `(r, beta)` with
  `B = lambda + d(r) + d(beta)` and `sigma` the row multiplier, this replaces
  the rank-one minimization lemma of the manuscript.
* `oneVariable_*`: for `h₀ > 0`, `Z > 0`, `C > 0` and any real `s`,
  `⨅ t, ((1 - s t Z)²/h₀ + C t² Z) = 1/(h₀ + s² Z/C)`, attained at
  `t = s/(C h₀ + s² Z)`. This is the final optimization of the degree-one
  coefficient. Because the infimum is taken over all real `t` with no
  normalization, the argument needs neither a division by the degree-zero
  coefficient `b` nor a separate `sin p₁ = 0` case.

Each is stated three ways: an exact algebraic identity for the difference,
the pointwise inequality (the form a later part integrates), and the value of
the infimum together with its minimizer.
-/

noncomputable section

namespace Manhattan.V4

/-! ## The scalar completion of the square -/

/-- The exact algebraic identity behind the scalar completion of the square. -/
theorem scalarCompletion_sub_eq {B sigma w v : ℝ} (hB : 0 < B) (hsigma : 0 ≤ sigma) :
    sigma * v ^ 2 + (w - sigma * v) ^ 2 / B - w ^ 2 / (B + sigma)
      = sigma * ((B + sigma) * v - w) ^ 2 / (B * (B + sigma)) := by
  have hBs : 0 < B + sigma := by linarith
  field_simp
  ring

/-- Pointwise form: the value `w²/(B + sigma)` is a lower bound for every `v`. -/
theorem scalarCompletion_le {B sigma w : ℝ} (hB : 0 < B) (hsigma : 0 ≤ sigma) (v : ℝ) :
    w ^ 2 / (B + sigma) ≤ sigma * v ^ 2 + (w - sigma * v) ^ 2 / B := by
  have hBs : 0 < B + sigma := by linarith
  have h := scalarCompletion_sub_eq (B := B) (sigma := sigma) (w := w) (v := v) hB hsigma
  have hnn : 0 ≤ sigma * ((B + sigma) * v - w) ^ 2 / (B * (B + sigma)) := by positivity
  linarith

/-- The minimizer `v = w/(B + sigma)` attains the value. -/
theorem scalarCompletion_eq {B sigma w : ℝ} (hB : 0 < B) (hsigma : 0 ≤ sigma) :
    sigma * (w / (B + sigma)) ^ 2 + (w - sigma * (w / (B + sigma))) ^ 2 / B
      = w ^ 2 / (B + sigma) := by
  have hBs : 0 < B + sigma := by linarith
  have h := scalarCompletion_sub_eq (B := B) (sigma := sigma) (w := w)
    (v := w / (B + sigma)) hB hsigma
  have hz : (B + sigma) * (w / (B + sigma)) - w = 0 := by
    field_simp
    ring
  rw [hz] at h
  have hzero : sigma * (0 : ℝ) ^ 2 / (B * (B + sigma)) = 0 := by simp
  linarith

/-- The scalar completion of the square, as an infimum. -/
theorem scalarCompletion_iInf {B sigma w : ℝ} (hB : 0 < B) (hsigma : 0 ≤ sigma) :
    ⨅ v : ℝ, (sigma * v ^ 2 + (w - sigma * v) ^ 2 / B) = w ^ 2 / (B + sigma) := by
  have hbdd : BddBelow (Set.range fun v : ℝ => sigma * v ^ 2 + (w - sigma * v) ^ 2 / B) := by
    refine ⟨w ^ 2 / (B + sigma), ?_⟩
    rintro x ⟨v, rfl⟩
    exact scalarCompletion_le hB hsigma v
  refine le_antisymm ?_ (le_ciInf fun v => scalarCompletion_le hB hsigma v)
  exact ciInf_le_of_le hbdd (w / (B + sigma)) (le_of_eq (scalarCompletion_eq hB hsigma))

/-! ## The one-variable minimization -/

/-- The exact algebraic identity behind the one-variable minimization. -/
theorem oneVariable_sub_eq {h0 Z s C t : ℝ} (hh0 : 0 < h0) (hZ : 0 < Z) (hC : 0 < C) :
    (1 - s * t * Z) ^ 2 / h0 + C * t ^ 2 * Z - 1 / (h0 + s ^ 2 * Z / C)
      = Z * (s - t * (C * h0 + s ^ 2 * Z)) ^ 2 / (h0 * (C * h0 + s ^ 2 * Z)) := by
  have hD : 0 < C * h0 + s ^ 2 * Z := by positivity
  have hd : h0 + s ^ 2 * Z / C = (C * h0 + s ^ 2 * Z) / C := by
    field_simp
  rw [hd]
  field_simp
  ring

/-- Pointwise form: `1/(h₀ + s² Z/C)` is a lower bound for every `t`. -/
theorem oneVariable_le {h0 Z s C : ℝ} (hh0 : 0 < h0) (hZ : 0 < Z) (hC : 0 < C) (t : ℝ) :
    1 / (h0 + s ^ 2 * Z / C) ≤ (1 - s * t * Z) ^ 2 / h0 + C * t ^ 2 * Z := by
  have hD : 0 < C * h0 + s ^ 2 * Z := by positivity
  have h := oneVariable_sub_eq (h0 := h0) (Z := Z) (s := s) (C := C) (t := t) hh0 hZ hC
  have hnn : 0 ≤ Z * (s - t * (C * h0 + s ^ 2 * Z)) ^ 2 / (h0 * (C * h0 + s ^ 2 * Z)) := by
    positivity
  linarith

/-- The minimizer `t = s/(C h₀ + s² Z)` attains the value. -/
theorem oneVariable_eq {h0 Z s C : ℝ} (hh0 : 0 < h0) (hZ : 0 < Z) (hC : 0 < C) :
    (1 - s * (s / (C * h0 + s ^ 2 * Z)) * Z) ^ 2 / h0
        + C * (s / (C * h0 + s ^ 2 * Z)) ^ 2 * Z
      = 1 / (h0 + s ^ 2 * Z / C) := by
  have hD : 0 < C * h0 + s ^ 2 * Z := by positivity
  have h := oneVariable_sub_eq (h0 := h0) (Z := Z) (s := s) (C := C)
    (t := s / (C * h0 + s ^ 2 * Z)) hh0 hZ hC
  have hz : s - s / (C * h0 + s ^ 2 * Z) * (C * h0 + s ^ 2 * Z) = 0 := by
    field_simp
    ring
  rw [hz] at h
  have hzero : Z * (0 : ℝ) ^ 2 / (h0 * (C * h0 + s ^ 2 * Z)) = 0 := by simp
  linarith

/-- The one-variable minimization, as an infimum. -/
theorem oneVariable_iInf {h0 Z s C : ℝ} (hh0 : 0 < h0) (hZ : 0 < Z) (hC : 0 < C) :
    ⨅ t : ℝ, ((1 - s * t * Z) ^ 2 / h0 + C * t ^ 2 * Z) = 1 / (h0 + s ^ 2 * Z / C) := by
  have hbdd : BddBelow (Set.range fun t : ℝ => (1 - s * t * Z) ^ 2 / h0 + C * t ^ 2 * Z) := by
    refine ⟨1 / (h0 + s ^ 2 * Z / C), ?_⟩
    rintro x ⟨t, rfl⟩
    exact oneVariable_le hh0 hZ hC t
  refine le_antisymm ?_ (le_ciInf fun t => oneVariable_le hh0 hZ hC t)
  exact ciInf_le_of_le hbdd (s / (C * h0 + s ^ 2 * Z)) (le_of_eq (oneVariable_eq hh0 hZ hC))

end Manhattan.V4
