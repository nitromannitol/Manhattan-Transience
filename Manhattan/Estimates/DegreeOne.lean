import Manhattan.Estimates.Elementary
import Mathlib.Data.Real.Sign

/-!
# The degree-one coefficient

The definitions here spell out all quadratic forms as weighted real-frequency
integrals, independently of the random environment. They are the statement
surface for Lemma 4.1.

Paper: `manuscript.tex:869-958`.
-/

open MeasureTheory Set

namespace Manhattan.Estimates

noncomputable section

/-- The degree-one coefficient `f_p` from (23). -/
noncomputable def degreeOneCoefficient (q : Parameters) (p₁ r : ℝ) : ℂ :=
  by
    classical
    exact if r ∈ q.supportInterval |p₁| then
      -Complex.I * (Real.sign (Real.sin p₁) : ℂ) / (Real.sin r : ℂ)
    else 0

/-- The positive normalization `b_p` in Lemma 4.1(a). -/
noncomputable def degreeOneNormalization (q : Parameters) (p₁ : ℝ) : ℝ :=
  by
    classical
    exact |Real.sin p₁| * torusIntegral (fun r : ℝ =>
      if r ∈ q.supportInterval |p₁| then (Real.sin r)⁻¹ else 0)

/-- **Guard lemma**, against the hazard
the audit recorded on E-011 (`ledger/ERRATA.md`). The manuscript's `k_p` carries the
multiplier `sgn(sin p₁)` (`manuscript.tex:1138-1141`), and `Real.sign 0 = 0`, so
a caller who dropped the hypothesis `hnormalization` could silently zero the
whole degree-three part of the competitor while every energy bound on it stayed
trivially true. That cannot happen: `degreeOneNormalization` has `|sin p₁|` as a
factor, so `degreeOneNormalization q p₁ ≠ 0` already forces `sin p₁ ≠ 0`. -/
theorem sin_ne_zero_of_degreeOneNormalization_ne_zero {q : Parameters} {p₁ : ℝ}
    (hnormalization : degreeOneNormalization q p₁ ≠ 0) : Real.sin p₁ ≠ 0 := by
  intro hsin
  exact hnormalization (by simp [degreeOneNormalization, hsin])

/-- The `sgn(sin p₁)` multiplier is nonzero wherever the normalization is.
 -/
theorem sign_sin_ne_zero_of_degreeOneNormalization_ne_zero {q : Parameters} {p₁ : ℝ}
    (hnormalization : degreeOneNormalization q p₁ ≠ 0) :
    Real.sign (Real.sin p₁) ≠ 0 := by
  simpa [Real.sign_eq_zero_iff] using
    sin_ne_zero_of_degreeOneNormalization_ne_zero hnormalization

/-- The complex form of the guard: the scalar the competitor multiplies its
degree-three part by is nonzero, hence a unit. -/
theorem ofReal_sign_sin_ne_zero_of_degreeOneNormalization_ne_zero
    {q : Parameters} {p₁ : ℝ} (hnormalization : degreeOneNormalization q p₁ ≠ 0) :
    ((Real.sign (Real.sin p₁) : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast sign_sin_ne_zero_of_degreeOneNormalization_ne_zero hnormalization

/-- The `sgn(sin p₁)` multiplier is unimodular wherever the normalization is
nonzero, so it moves no norm and no energy. -/
theorem abs_sign_sin_of_degreeOneNormalization_ne_zero {q : Parameters} {p₁ : ℝ}
    (hnormalization : degreeOneNormalization q p₁ ≠ 0) :
    |Real.sign (Real.sin p₁)| = 1 := by
  rcases lt_trichotomy (Real.sin p₁) 0 with hlt | heq | hgt
  · rw [Real.sign_of_neg hlt]; norm_num
  · exact absurd heq (sin_ne_zero_of_degreeOneNormalization_ne_zero hnormalization)
  · rw [Real.sign_of_pos hgt]; norm_num

/-- The signed indicator which is the exact mixed residual. -/
noncomputable def signedSupportIndicator (q : Parameters) (p₁ r : ℝ) : ℂ :=
  by
    classical
    exact if r ∈ q.supportInterval |p₁| then (Real.sign (Real.sin p₁) : ℂ) else 0

/-- The degree-zero adjoint applied to a one-row coefficient. -/
noncomputable def degreeZeroAdjoint (p₁ : ℝ) (f : ℝ → ℂ) : ℂ :=
  -Complex.I * (Real.sin p₁ : ℂ) * torusIntegral f

/-- The degree-one `H₁` quadratic form, with multiplier `λ+d(p₁)+d(r)`. -/
noncomputable def degreeOneEnergy (q : Parameters) (p₁ : ℝ) : ℝ :=
  torusIntegral (fun r : ℝ =>
    (q.lambda + dispersion p₁ + dispersion r) * ‖degreeOneCoefficient q p₁ r‖ ^ 2)

/-- The mixed residual `i sin(r) f_p(r)`. -/
noncomputable def mixedResidual (q : Parameters) (p₁ r : ℝ) : ℂ :=
  Complex.I * (Real.sin r : ℂ) * degreeOneCoefficient q p₁ r

/-- The explicit squared mixed `H⁻¹` norm in Lemma 4.1(c). -/
noncomputable def mixedResidualHMinusSq (q : Parameters) (p₁ : ℝ) : ℝ :=
  torusIntegral (fun r : ℝ => torusIntegral (fun beta : ℝ =>
    mixedHMinusWeight q r beta * ‖mixedResidual q p₁ r‖ ^ 2))

/-- The explicit squared two-row `H⁻¹` norm in Lemma 4.1(d).

The coefficient is passed explicitly so the definition does not smuggle any
probability-model or tuple-normalization convention into this file.
-/
noncomputable def twoRowResidualHMinusSq (q : Parameters) (p₁ p₂ : ℝ)
    (f : ℝ → ℂ) : ℝ :=
  torusIntegral (fun r : ℝ => torusIntegral (fun r' : ℝ =>
    let alpha := r + r' - p₂
    twoRowHMinusWeight q p₁ alpha *
      ‖Complex.I * (Real.sin p₁ : ℂ) * (f r + f r')‖ ^ 2))

/-- On its support, `sin r` cannot vanish once the lower endpoint is positive
and the upper endpoint is below `π`. -/
theorem sin_ne_zero_on_support {q : Parameters} {a r : ℝ}
    (hleft : 0 < q.K * q.delta a) (hright : q.r0 < Real.pi)
    (hr : r ∈ q.supportInterval a) : Real.sin r ≠ 0 := by
  have hrpos : 0 < r := hleft.trans_le hr.1
  have hrpi : r < Real.pi := hr.2.trans_lt hright
  exact (Real.sin_pos_of_mem_Ioo ⟨hrpos, hrpi⟩).ne'

/-- Lemma 4.1(c), algebraic part: the mixed residual is exactly the signed
indicator of `I`. -/
theorem mixedResidual_eq_indicator {q : Parameters} {p₁ r : ℝ}
    (hleft : 0 < q.K * q.delta |p₁|) (hright : q.r0 < Real.pi) :
    mixedResidual q p₁ r = signedSupportIndicator q p₁ r := by
  classical
  by_cases hr : r ∈ q.supportInterval |p₁|
  · have hsin := sin_ne_zero_on_support hleft hright hr
    have hsinComplex : (Real.sin r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hsin
    simp only [mixedResidual, degreeOneCoefficient, signedSupportIndicator, hr, if_pos]
    field_simp
    simp [Complex.I_sq]
  · simp [mixedResidual, degreeOneCoefficient, signedSupportIndicator, hr]

end

end Manhattan.Estimates
