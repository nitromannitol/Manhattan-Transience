import Manhattan.Estimates.Elementary

/-!
# Rank-one minimization and the multiplier

Paper: `manuscript.tex:960-1000` (equations (26)--(29)).
-/

open MeasureTheory Set

namespace Manhattan.Estimates

noncomputable section

/-- The scalar `σ = |η|² ∫_J M⁻¹ dm` in (26). -/
noncomputable def rankOneSigma (eta : ℂ) (M : ℝ → ℝ) (J : Set ℝ) : ℝ :=
  by
    classical
    exact ‖eta‖ ^ 2 * torusIntegral (fun alpha : ℝ =>
      if alpha ∈ J then (M alpha)⁻¹ else 0)

/-- The rank-one objective in (26), written on normalized torus measure. -/
noncomputable def rankOneEnergy (B : ℝ) (M : ℝ → ℝ) (J : Set ℝ)
    (eta w : ℂ) (u : ℝ → ℂ) : ℝ :=
  by
    classical
    exact torusIntegral (fun alpha : ℝ =>
      if alpha ∈ J then M alpha * ‖u alpha‖ ^ 2 else 0) +
      B⁻¹ * ‖w - eta * torusIntegral (fun alpha : ℝ =>
        if alpha ∈ J then u alpha else 0)‖ ^ 2

/-- The explicit minimizer in (27). -/
noncomputable def rankOneMinimizer (B : ℝ) (M : ℝ → ℝ) (J : Set ℝ)
    (eta w : ℂ) (alpha : ℝ) : ℂ :=
  by
    classical
    exact if alpha ∈ J then
      (star eta * w) / ((M alpha : ℂ) * (B + rankOneSigma eta M J))
    else 0

/-- The multiplier `M` from (28). -/
def multiplier (kappa : ℝ) (q : Parameters) (P : Fin 2 → ℝ) : ℝ :=
  kappa * (q.lambda + theta P + 2 * |Real.sin (P 0 / 2)| +
    2 * |Real.sin (P 1 / 2)|)

/-- The mixed total frequency `(β,α)`. -/
def mixedTotalFrequency (beta alpha : ℝ) : Fin 2 → ℝ := ![beta, alpha]

/-- The multiplier is nonnegative for nonnegative `κ` and `λ`. -/
theorem multiplier_nonneg {kappa : ℝ} {q : Parameters}
    (hkappa : 0 ≤ kappa) (hlam : 0 ≤ q.lambda) (P : Fin 2 → ℝ) :
    0 ≤ multiplier kappa q P := by
  apply mul_nonneg hkappa
  have hθ := theta_nonneg P
  positivity

/-- The multiplier is strictly positive when both `κ` and `λ` are positive. -/
theorem multiplier_pos {kappa : ℝ} {q : Parameters}
    (hkappa : 0 < kappa) (hlam : 0 < q.lambda) (P : Fin 2 → ℝ) :
    0 < multiplier kappa q P := by
  apply mul_pos hkappa
  have hθ := theta_nonneg P
  positivity

/-- The one-dimensional estimate used in Lemma 5.2 after applying (22). -/
theorem sine_sq_div_sqrt_le (lambda x : ℝ) (hlam : 0 ≤ lambda) :
    Real.sin x ^ 2 / Real.sqrt (lambda + dispersion x) ≤
      2 * Real.sqrt 2 * |Real.sin (x / 2)| := by
  have hd : dispersion x = 2 * Real.sin (x / 2) ^ 2 := by
    unfold dispersion
    rw [show Real.cos x = Real.cos (2 * (x / 2)) by congr 1; ring,
      Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq (x / 2)]
  have hsin : Real.sin x = 2 * Real.sin (x / 2) * Real.cos (x / 2) := by
    calc
      Real.sin x = Real.sin (x / 2 + x / 2) := by congr 1; ring
      _ = 2 * Real.sin (x / 2) * Real.cos (x / 2) := by
        rw [Real.sin_add]
        ring
  rw [hd]
  by_cases hx : Real.sin (x / 2) = 0
  · simp [hsin, hx]
  · have hsqrt : Real.sqrt (2 * Real.sin (x / 2) ^ 2) =
        Real.sqrt 2 * |Real.sin (x / 2)| := by
      rw [Real.sqrt_mul (by positivity : 0 ≤ (2 : ℝ)), Real.sqrt_sq_eq_abs]
    have hden : Real.sqrt (2 * Real.sin (x / 2) ^ 2) ≤
        Real.sqrt (lambda + 2 * Real.sin (x / 2) ^ 2) := by
      exact Real.sqrt_le_sqrt (by linarith)
    have hpos : 0 < Real.sqrt (2 * Real.sin (x / 2) ^ 2) := by positivity
    rw [hsin]
    calc
      (2 * Real.sin (x / 2) * Real.cos (x / 2)) ^ 2 /
          Real.sqrt (lambda + 2 * Real.sin (x / 2) ^ 2)
          ≤ (2 * Real.sin (x / 2) * Real.cos (x / 2)) ^ 2 /
            Real.sqrt (2 * Real.sin (x / 2) ^ 2) := by
              exact div_le_div_of_nonneg_left (sq_nonneg _) hpos hden
      _ ≤ 2 * Real.sqrt 2 * |Real.sin (x / 2)| := by
        rw [hsqrt]
        have hroot : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
        field_simp
        rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), sq_abs]
        nlinarith [Real.sin_sq_add_cos_sq (x / 2), sq_nonneg (Real.sin (x / 2))]

/-- The pointwise scalar expression left after the line-frequency integral in
the proof of Lemma 5.2. The factor eight safely absorbs the four-term square
and the two directions. -/
def fourEstimateCore (q : Parameters) (P : Fin 2 → ℝ) : ℝ :=
  hWeight q P + 8 *
    (Real.sin (P 0) ^ 2 / Real.sqrt (q.lambda + dispersion (P 0)) +
     Real.sin (P 1) ^ 2 / Real.sqrt (q.lambda + dispersion (P 1)))

/-- The multiplier is linear in its constant. -/
theorem multiplier_eq_smul (kappa : ℝ) (q : Parameters) (P : Fin 2 → ℝ) :
    multiplier kappa q P = kappa * multiplier 1 q P := by
  simp only [multiplier]; ring

/-- The multiplier is monotone in its constant. -/
theorem multiplier_mono {q : Parameters} {kappa kappa' : ℝ} (hle : kappa ≤ kappa')
    (hlam : 0 ≤ q.lambda) (P : Fin 2 → ℝ) :
    multiplier kappa q P ≤ multiplier kappa' q P := by
  have hth := theta_nonneg P
  have h0 := abs_nonneg (Real.sin (P 0 / 2))
  have h1 := abs_nonneg (Real.sin (P 1 / 2))
  simp only [multiplier]
  nlinarith [hle, hlam, hth, h0, h1]

/-- The scalar step bounds each `sin²(Pᵢ)/√(λ+d(Pᵢ))` by `2√2 |sin(Pᵢ/2)|`, so
`fourEstimateCore` is under `8√2 = 11.31…` times the multiplier and `κ = 12`
suffices where the universal choice below takes `40`. -/
theorem fourEstimateCore_le_multiplier_twelve {q : Parameters} (hlam : 0 ≤ q.lambda)
    (P : Fin 2 → ℝ) : fourEstimateCore q P ≤ multiplier 12 q P := by
  have hzero := sine_sq_div_sqrt_le q.lambda (P 0) hlam
  have hone := sine_sq_div_sqrt_le q.lambda (P 1) hlam
  have hsqrt : Real.sqrt 2 ≤ 3/2 := by linarith [Real.sqrt_two_lt_three_halves]
  have habs0 : 0 ≤ |Real.sin (P 0 / 2)| := abs_nonneg _
  have habs1 : 0 ≤ |Real.sin (P 1 / 2)| := abs_nonneg _
  have hth := theta_nonneg P
  simp only [fourEstimateCore, multiplier, hWeight] at *
  nlinarith [hzero, hone, hsqrt, habs0, habs1, hth, hlam]

/-- The scalar step at any constant at least `12`. -/
theorem fourEstimateCore_le_multiplier_of_twelve_le {q : Parameters} {kappa : ℝ}
    (hkappa : 12 ≤ kappa) (hlam : 0 ≤ q.lambda) (P : Fin 2 → ℝ) :
    fourEstimateCore q P ≤ multiplier kappa q P :=
  (fourEstimateCore_le_multiplier_twelve hlam P).trans (multiplier_mono hkappa hlam P)

/-- Lemma 5.2's scalar `κ` bound, with the universal choice `κ = 40`. -/
theorem fourEstimateCore_le_multiplier {q : Parameters} (hlam : 0 ≤ q.lambda)
    (P : Fin 2 → ℝ) : fourEstimateCore q P ≤ multiplier 40 q P := by
  have hzero := sine_sq_div_sqrt_le q.lambda (P 0) hlam
  have hone := sine_sq_div_sqrt_le q.lambda (P 1) hlam
  have hsqrt : Real.sqrt 2 ≤ 2 := by linarith [Real.sqrt_two_lt_three_halves]
  have habs0 : 0 ≤ |Real.sin (P 0 / 2)| := abs_nonneg _
  have habs1 : 0 ≤ |Real.sin (P 1 / 2)| := abs_nonneg _
  have htheta := theta_nonneg P
  dsimp [fourEstimateCore, multiplier, hWeight]
  nlinarith

/-- Equation (29) with explicit uniform constants for the fixed choice
`κ = 40`. -/
theorem multiplier_comparison_explicit {K rho lambda beta alpha : ℝ}
    (hK : 20 ≤ K) (hrho : rho ≤ Real.pi / 20)
    (hlam : 0 < lambda) (hlamOne : lambda ≤ 1)
    (halphaRho : |alpha| ≤ rho)
    (hseparation : 4 * K * (Real.sqrt lambda + |beta|) ≤ |alpha|) :
    let q : Parameters := ⟨lambda, K, rho⟩
    (80 / Real.pi) * |alpha| ≤ multiplier 40 q (mixedTotalFrequency beta alpha) ∧
      multiplier 40 q (mixedTotalFrequency beta alpha) ≤ 200 * |alpha| := by
  dsimp
  have hlamNonneg : 0 ≤ lambda := hlam.le
  have hsqrtNonneg : 0 ≤ Real.sqrt lambda := Real.sqrt_nonneg _
  have hsumNonneg : 0 ≤ Real.sqrt lambda + |beta| :=
    add_nonneg hsqrtNonneg (abs_nonneg _)
  have hKmul : 4 * 20 * (Real.sqrt lambda + |beta|) ≤
      4 * K * (Real.sqrt lambda + |beta|) := by
    gcongr
  have hsmall : 80 * (Real.sqrt lambda + |beta|) ≤ |alpha| :=
    by
      calc
        80 * (Real.sqrt lambda + |beta|) =
            4 * 20 * (Real.sqrt lambda + |beta|) := by ring
        _ ≤ |alpha| := hKmul.trans hseparation
  have hsqrtSmall : Real.sqrt lambda ≤ |alpha| / 80 := by nlinarith [abs_nonneg beta]
  have hbetaSmall : |beta| ≤ |alpha| / 80 := by nlinarith
  have hsqrtSq : (Real.sqrt lambda) ^ 2 = lambda := Real.sq_sqrt hlamNonneg
  have hlamSqrt : lambda ≤ Real.sqrt lambda := by
    nlinarith [sq_nonneg (1 - Real.sqrt lambda)]
  have halphaOne : |alpha| ≤ 1 := by
    linarith [Real.pi_le_four]
  have hbetaOne : |beta| ≤ 1 := by
    have : |alpha| / 80 ≤ 1 := by nlinarith [abs_nonneg alpha]
    exact hbetaSmall.trans this
  have hdispAlpha := dispersion_le_half_mul_sq alpha
  have hdispBeta := dispersion_le_half_mul_sq beta
  have halphaSq : alpha ^ 2 ≤ |alpha| := by
    rw [← sq_abs]
    nlinarith [abs_nonneg alpha]
  have hbetaSq : beta ^ 2 ≤ |beta| := by
    rw [← sq_abs]
    nlinarith [abs_nonneg beta]
  have hsinAlpha : 2 * |Real.sin (alpha / 2)| ≤ |alpha| := by
    calc
      2 * |Real.sin (alpha / 2)| ≤ 2 * |alpha / 2| := by
        exact mul_le_mul_of_nonneg_left
          (Real.abs_sin_le_abs : |Real.sin (alpha / 2)| ≤ |alpha / 2|) (by norm_num)
      _ = |alpha| := by rw [abs_div]; norm_num; ring
  have hsinBeta : 2 * |Real.sin (beta / 2)| ≤ |beta| := by
    calc
      2 * |Real.sin (beta / 2)| ≤ 2 * |beta / 2| := by
        exact mul_le_mul_of_nonneg_left
          (Real.abs_sin_le_abs : |Real.sin (beta / 2)| ≤ |beta / 2|) (by norm_num)
      _ = |beta| := by rw [abs_div]; norm_num; ring
  have hhalfAlpha : |alpha / 2| ≤ Real.pi / 2 := by
    have hpi : Real.pi / 20 ≤ Real.pi / 2 := by
      nlinarith [Real.pi_pos]
    calc
      |alpha / 2| = |alpha| / 2 := by rw [abs_div]; norm_num
      _ ≤ |alpha| := by nlinarith [abs_nonneg alpha]
      _ ≤ Real.pi / 2 := halphaRho.trans (hrho.trans hpi)
  have hjordan := Real.mul_abs_le_abs_sin hhalfAlpha
  have hlowerSin : (2 / Real.pi) * |alpha| ≤
      2 * |Real.sin (alpha / 2)| := by
    calc
      (2 / Real.pi) * |alpha| =
          2 * ((2 / Real.pi) * |alpha / 2|) := by
        rw [abs_div]
        norm_num
        ring
      _ ≤ 2 * |Real.sin (alpha / 2)| :=
        mul_le_mul_of_nonneg_left hjordan (by norm_num)
  constructor
  · simp only [multiplier, mixedTotalFrequency, theta, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    have hnonneg : 0 ≤ lambda + (dispersion beta + dispersion alpha) +
        2 * |Real.sin (beta / 2)| := by
      exact add_nonneg
        (add_nonneg hlamNonneg
          (add_nonneg (dispersion_nonneg beta) (dispersion_nonneg alpha)))
        (mul_nonneg (by norm_num) (abs_nonneg _))
    calc
      (80 / Real.pi) * |alpha| =
          40 * ((2 / Real.pi) * |alpha|) := by ring
      _ ≤ 40 * (2 * |Real.sin (alpha / 2)|) :=
        mul_le_mul_of_nonneg_left hlowerSin (by norm_num)
      _ ≤ 40 * (lambda + (dispersion beta + dispersion alpha) +
          2 * |Real.sin (beta / 2)| + 2 * |Real.sin (alpha / 2)|) := by
        gcongr
        exact le_add_of_nonneg_left hnonneg
  · simp only [multiplier, mixedTotalFrequency, theta, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    clear hrho halphaRho hhalfAlpha hjordan hlowerSin
    nlinarith [dispersion_nonneg alpha, dispersion_nonneg beta, abs_nonneg alpha,
      abs_nonneg beta]

end

end Manhattan.Estimates
