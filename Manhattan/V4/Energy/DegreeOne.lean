import Manhattan.Glue.ConcreteLowering
import Manhattan.V4.Energy.Weight

/-!
# Version 4, Move 1: the degree-one facts and the degree-one cost

Ingredients (a) and (b) of Move 1 of the Version 4 argument.

* (a) For the purely imaginary degree-one profile `f = -i φ` with `φ` real,
  `D₀* f = - sin(p₁) ∫ φ dm`, and the row symbol is `w(r) = sin(r) φ(r)`,
  which is **odd** when `φ` is even. The first is a direct specialization of
  `Manhattan.Glue.dStarZero_degreeOneRealFrequency` (already proved in the sealed
  development, `Manhattan/Glue/ConcreteLowering.lean`); the minus sign is that
  lemma's and is not in dispute here.
* (b) Estimate (4): with `μ = λ + d(p₁) ≤ δ²` and `s² ≤ 2μ`, the row multiplier
  `μ + d(r) + 2 s² J(μ)`, `J(μ) = 1/√(μ(μ+2))`, is at most `6 (δ + r²)`.
  The factor `2 s²/√(μ(μ+2))` is the two-row contraction produced by integrating
  the second row frequency.
-/

open MeasureTheory

namespace Manhattan.V4.Energy

/-! ## (a) the degree-one lowering coefficient -/

/-- The normalized torus integral commutes with the real-to-complex coercion. -/
theorem torusIntegral_ofReal (phi : ℝ → ℝ) :
    Manhattan.Estimates.torusIntegral (fun r => ((phi r : ℝ) : ℂ))
      = ((Manhattan.Estimates.torusIntegral phi : ℝ) : ℂ) := by
  unfold Manhattan.Estimates.torusIntegral
  rw [integral_complex_ofReal]
  simp only [Complex.real_smul, smul_eq_mul, Complex.ofReal_mul]

/-- **Version 4, degree-one fact (a).** For the purely imaginary profile
`f = -i φ` with `φ` real, `D₀* f = - sin(p₁) ∫ φ dm`. This is the uncancelled
degree-zero component of the Version 4 competitor: it is what produces the
numerator `1 - s ∫ φ dm` in Move 1 (1). -/
theorem dStarZero_neg_I_mul (p : Fin 2 → ℝ) (phi : ℝ → ℝ)
    (hf : MemLp (fun r => -Complex.I * ((phi r : ℝ) : ℂ)) 2
      (volume.restrict (Set.Ioc (-Real.pi) Real.pi))) :
    Manhattan.Glue.loweringCoefficient p
        (Manhattan.degreeOneRealFrequencySynthesis Manhattan.Axis.horizontal
          (fun r => -Complex.I * ((phi r : ℝ) : ℂ)) hf) ∅
      = ((-(Real.sin (p 0) * Manhattan.Estimates.torusIntegral phi) : ℝ) : ℂ) := by
  rw [Manhattan.Glue.dStarZero_degreeOneRealFrequency p
    (fun r => -Complex.I * ((phi r : ℝ) : ℂ)) hf]
  have h1 : Manhattan.Estimates.torusIntegral (fun r => -Complex.I * ((phi r : ℝ) : ℂ))
      = -Complex.I * Manhattan.Estimates.torusIntegral (fun r => ((phi r : ℝ) : ℂ)) := by
    unfold Manhattan.Estimates.torusIntegral
    rw [integral_const_mul]
    simp only [Complex.real_smul]
    ring
  rw [h1, torusIntegral_ofReal phi]
  push_cast
  have hI2 : (Complex.I : ℂ) ^ 2 = -1 := by norm_num
  calc -(Complex.I * Complex.sin ((p 0 : ℝ) : ℂ)) *
        (-Complex.I * ((Manhattan.Estimates.torusIntegral phi : ℝ) : ℂ))
      = (Complex.I ^ 2) * (Complex.sin ((p 0 : ℝ) : ℂ) *
          ((Manhattan.Estimates.torusIntegral phi : ℝ) : ℂ)) := by ring
    _ = (-1 : ℂ) * (Complex.sin ((p 0 : ℝ) : ℂ) *
          ((Manhattan.Estimates.torusIntegral phi : ℝ) : ℂ)) := by rw [hI2]
    _ = -(Complex.sin ((p 0 : ℝ) : ℂ) *
          ((Manhattan.Estimates.torusIntegral phi : ℝ) : ℂ)) := by ring

/-- The degree-one row symbol `w(r) = sin(r) φ(r)`. -/
noncomputable def rowSymbol (phi : ℝ → ℝ) (r : ℝ) : ℝ := Real.sin r * phi r

/-- **Version 4, degree-one fact (a), parity.** `w` is odd whenever `φ` is even.
This is the single hypothesis that drives all four parity cancellations of
Step 3 of the Version 4 argument. -/
theorem rowSymbol_odd {phi : ℝ → ℝ} (h : ∀ r, phi (-r) = phi r) (r : ℝ) :
    rowSymbol phi (-r) = -rowSymbol phi r := by
  unfold rowSymbol
  rw [Real.sin_neg, h r]
  ring

/-! ## (b) the degree-one cost, estimate (4) -/

/-- **Estimate (4) of Version 4, pointwise in the row frequency.** Here
`mu = λ + d(p₁)`, `s = sin p₁`, and the third summand is the two-row contraction
`2 s² J(mu)` with `J(mu) = 1/√(mu(mu+2))`. The hypotheses `mu ≤ δ²` and
`s² ≤ 2 mu` are the ones the manuscript records. -/
theorem degreeOne_multiplier_le {mu delta s r : ℝ}
    (hmu : 0 < mu) (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hmud : mu ≤ delta ^ 2) (hs : s ^ 2 ≤ 2 * mu) :
    mu + Manhattan.Estimates.dispersion r + 2 * s ^ 2 / Real.sqrt (mu * (mu + 2))
      ≤ 6 * (delta + r ^ 2) := by
  have disp_bound : Manhattan.Estimates.dispersion r ≤ (1 / 2 : ℝ) * r ^ 2 :=
    Manhattan.Estimates.dispersion_le_half_mul_sq r
  have mu_le_delta : mu ≤ delta := by nlinarith [sq_nonneg delta]
  have h_2mu_pos : 0 < 2 * mu := by nlinarith
  have h_2mu_le : 2 * mu ≤ mu * (mu + 2) := by nlinarith
  have h_sqrt_le : Real.sqrt (2 * mu) ≤ Real.sqrt (mu * (mu + 2)) :=
    Real.sqrt_le_sqrt h_2mu_le
  have h_sqrt_2mu_pos : 0 < Real.sqrt (2 * mu) := Real.sqrt_pos.mpr h_2mu_pos
  have h_s_bound : 2 * s ^ 2 ≤ 4 * mu := by nlinarith
  have h_denom_pos : 0 < Real.sqrt (mu * (mu + 2)) := Real.sqrt_pos.mpr (by nlinarith)
  have h_div_bound : 2 * s ^ 2 / Real.sqrt (mu * (mu + 2))
      ≤ 4 * mu / Real.sqrt (2 * mu) := by
    calc 2 * s ^ 2 / Real.sqrt (mu * (mu + 2))
        ≤ 4 * mu / Real.sqrt (mu * (mu + 2)) :=
          div_le_div_of_nonneg_right h_s_bound h_denom_pos.le
      _ ≤ 4 * mu / Real.sqrt (2 * mu) :=
          div_le_div_of_nonneg_left (by nlinarith) h_sqrt_2mu_pos h_sqrt_le
  have h_sqrt_bound : Real.sqrt (2 * mu) ≤ 2 * delta := by
    have h_sq_bound : 2 * mu ≤ (2 * delta) ^ 2 := by nlinarith
    rw [← Real.sqrt_sq (by nlinarith : (0:ℝ) ≤ 2 * delta)]
    exact Real.sqrt_le_sqrt h_sq_bound
  have h_third_bound : 2 * s ^ 2 / Real.sqrt (mu * (mu + 2)) ≤ 4 * delta := by
    have h_sqrt_sq : Real.sqrt (2 * mu) ^ 2 = 2 * mu := Real.sq_sqrt (by nlinarith)
    have h_ineq_no_div : (4 * mu : ℝ) ≤ 4 * delta * Real.sqrt (2 * mu) := by
      nlinarith [h_sqrt_bound, h_sqrt_sq, h_sqrt_2mu_pos, sq_nonneg delta]
    have := (div_le_iff₀ h_sqrt_2mu_pos).mpr h_ineq_no_div
    linarith [h_div_bound, this]
  nlinarith [disp_bound, mu_le_delta, h_third_bound, sq_nonneg r]

end Manhattan.V4.Energy
