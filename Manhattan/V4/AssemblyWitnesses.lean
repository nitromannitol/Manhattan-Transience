import Manhattan.V4.CompetitorEnergy
import Manhattan.V4.Frequency.Uniform
import Manhattan.V4.Energy.Witnesses

/-!
# The non-degeneracy certificates

Every composed statement of  gets a witness here: explicit parameters
satisfying all of its hypotheses simultaneously, and, wherever it is an
inequality, a proof that the inequality is **strict** at explicit data, so that
no link of the chain can be `X ≤ X` after unfolding.

* The fibre integral.  `parityJ_pos` rules out the Bochner junk value; `strict_parityJ_ge`
  proves `parityJ_ge` strict at `r = 3π`, where the torus distance `|r|_𝕋 = π`
  is strictly below `|r| = 3π`; `nonvacuity_parity_betaIntegral_le` and
  `strict_paritySigma_inner_lower` exhibit `κ = 120`, `δ = 1/100`, `r = 1/5`,
  `λ = 1/2`, `β = 1/10` satisfying every hypothesis with both sides strictly
  positive.
* The degree-one summand.  `strict_degreeOne_symbol_le`,
  `nonvacuity_degreeOne_symbol_le`.
* The scalar completion at the parity minimizer.
  `strict_paritySigmaEnergy_pointwise`: the degree-three density is
  **strictly** below the Move 1 density whenever the row profile does not
  vanish, the gap being exactly the degree-two residual `B v²`.
* The complementary region.  `strict_driftlessMajorant_le_v4Majorant` at
  `λ = 1`, `r₀ = 1/4`, `p = (π, π)`, where the two sides are `1/5` and
  `outerRegionConstant(1/4)/(1 + π²) ≥ (π²/2)/(1 + π²)`.
* The composed competitor cost.  `nonvacuity_v4_competitor_cost_le` instantiates
  `v4_competitor_cost_le` at `κ = 120`, `δ = 1/100`, `r₀ = 1/4`, `λ = 1/2`,
  `C₁ = 6`, `C₃ = 9` and indicator `testPhi`, which
  `testPhi_nondegenerate` shows is **not** the zero function.
* The fixed-frequency bound.  `v4FrequencyBound_outer_verified` proves the
  target inequality of `V4FrequencyBound` unconditionally on the whole
  complementary region, and `v4Majorant_nondegenerate` shows the majorant is a
  genuine positive real everywhere.
-/

noncomputable section

open MeasureTheory

namespace Manhattan.V4

/-! ### The fibre integral -/

/-- `J` is strictly positive: the closed form is a logarithm of something
strictly bigger than one, so `parityJ` is never the Bochner junk value. -/
theorem parityJ_pos {kappa delta : ℝ} (hkappa : 0 < kappa) (hdelta : 0 < delta)
    (r beta : ℝ) : 0 < parityJ kappa delta r beta := by
  rw [parityJ_eq hkappa hdelta r beta]
  have hA : 0 < delta + torusAbs r + torusAbs beta := by
    have := torusAbs_nonneg r
    have := torusAbs_nonneg beta
    linarith
  have hlog : 0 < Real.log (1 + Real.pi / (delta + torusAbs r + torusAbs beta)) := by
    refine Real.log_pos ?_
    have : 0 < Real.pi / (delta + torusAbs r + torusAbs beta) := by positivity
    linarith
  positivity

theorem torusAbs_three_pi : torusAbs (3 * Real.pi) = Real.pi := by
  have hper : torusAbs (Real.pi + 2 * Real.pi) = torusAbs Real.pi := torusAbs_periodic Real.pi
  have hpi : Real.pi ∈ Estimates.torus := ⟨by linarith [Real.pi_pos], le_rfl⟩
  have h3 : (3 : ℝ) * Real.pi = Real.pi + 2 * Real.pi := by ring
  rw [h3, hper, torusAbs_eq_abs hpi, abs_of_pos Real.pi_pos]

/-- **`parityJ_ge` is strict**, so the two sides are not the same term: at
`r = 3π` the torus distance `|r|_𝕋 = π` is strictly below `|r| = 3π`. -/
theorem strict_parityJ_ge :
    (1 * Real.pi)⁻¹ * Real.log (1 + Real.pi / (1 + |(3 : ℝ) * Real.pi| + |(0 : ℝ)|))
      < parityJ 1 1 (3 * Real.pi) 0 := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  rw [parityJ_eq (by norm_num) (by norm_num) (3 * Real.pi) 0]
  have h0 : torusAbs (0 : ℝ) = 0 := by
    have hmem : (0:ℝ) ∈ Estimates.torus := ⟨by linarith, by linarith⟩
    rw [torusAbs_eq_abs hmem, abs_zero]
  rw [torusAbs_three_pi, h0]
  have habs : |(3 : ℝ) * Real.pi| = 3 * Real.pi := abs_of_pos (by linarith)
  have habs0 : |(0 : ℝ)| = 0 := abs_zero
  rw [habs, habs0]
  refine mul_lt_mul_of_pos_left ?_ (by positivity)
  refine Real.log_lt_log (by positivity) ?_
  have hlt : Real.pi / (1 + 3 * Real.pi + 0) < Real.pi / (1 + Real.pi + 0) := by
    apply div_lt_div_of_pos_left hpi (by linarith) (by linarith)
  linarith

/-- Every hypothesis of `parity_betaIntegral_le` is satisfiable at explicit
parameters, with `σ` not forced to vanish. -/
theorem nonvacuity_parity_betaIntegral_le :
    (0:ℝ) < 120 ∧ (0:ℝ) < 1 / 100 ∧ (1 / 100 : ℝ) ≤ |(1 / 5 : ℝ)| ^ 2
      ∧ (0:ℝ) < 1 / 2 ∧ (0:ℝ) < |(1 / 5 : ℝ)| ∧ |(1 / 5 : ℝ)| ≤ 1 / 4 := by
  refine ⟨by norm_num, by norm_num, ?_, by norm_num, ?_, ?_⟩
  · rw [abs_of_pos (by norm_num : (0:ℝ) < 1 / 5)]; norm_num
  · rw [abs_of_pos (by norm_num : (0:ℝ) < 1 / 5)]; norm_num
  · rw [abs_of_pos (by norm_num : (0:ℝ) < 1 / 5)]; norm_num

/-- The inner lower bound on `σ` is non-degenerate: at `β = 1/10` its left-hand
side is strictly positive, so the estimate is not `0 ≤ 0`. -/
theorem strict_paritySigma_inner_lower :
    0 < 2 / (Real.pi ^ 3 * 120) * ((1 / 10 : ℝ) ^ 2 * Real.log (1 / |(1 / 5 : ℝ)|))
      ∧ 2 / (Real.pi ^ 3 * 120) * ((1 / 10 : ℝ) ^ 2 * Real.log (1 / |(1 / 5 : ℝ)|))
        ≤ paritySigma 120 (1 / 100) (1 / 5) (1 / 10) := by
  have habs : |(1 / 5 : ℝ)| = 1 / 5 := abs_of_pos (by norm_num)
  have hlog : 0 < Real.log (1 / |(1 / 5 : ℝ)|) := by
    rw [habs]
    exact Real.log_pos (by norm_num)
  constructor
  · have hpi : (0:ℝ) < Real.pi := Real.pi_pos
    positivity
  · refine paritySigma_inner_lower (by norm_num) (by norm_num) ?_ ?_ ?_ ?_
    · rw [habs]; norm_num
    · rw [habs]; norm_num
    · rw [habs]; norm_num
    · rw [abs_of_pos (by norm_num : (0:ℝ) < 1 / 10), habs]
      have h : Real.sqrt (1 / 25 : ℝ) ≤ Real.sqrt (1 / 5 : ℝ) :=
        Real.sqrt_le_sqrt (by norm_num)
      have h25 : Real.sqrt (1 / 25 : ℝ) = 1 / 5 := by
        rw [show (1 / 25 : ℝ) = (1 / 5) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      rw [h25] at h
      linarith

/-! ### The degree-one summand -/

/-- **`degreeOne_symbol_le` is strict**: at `μ = 1/100`, `δ = 1/10`, `r = 0` the
two sides are `1/100` and `3/5`. -/
theorem strict_degreeOne_symbol_le :
    (1 / 100 : ℝ) + Manhattan.Estimates.dispersion 0 < 6 * ((1 / 10 : ℝ) + 0 ^ 2) := by
  have h : Manhattan.Estimates.dispersion 0 = 0 := by
    unfold Manhattan.Estimates.dispersion
    simp
  rw [h]
  norm_num

/-- The hypotheses of `degreeOne_symbol_le` hold at those parameters. -/
theorem nonvacuity_degreeOne_symbol_le :
    (0:ℝ) < 1 / 100 ∧ (0:ℝ) < 1 / 10 ∧ (1 / 10 : ℝ) ≤ 1
      ∧ (1 / 100 : ℝ) ≤ (1 / 10 : ℝ) ^ 2 := by
  norm_num

/-! ### The scalar completion at the parity minimizer -/

/-- **The degree-three density is strictly below the Move 1 density** whenever
the row profile does not vanish: the gap is exactly the degree-two residual
`(w - σ v)²/B = B v²`. -/
theorem strict_paritySigmaEnergy_pointwise {kappa delta w : ℝ}
    {q : Estimates.Parameters} (hlam : 0 < q.lambda) (hkappa : 0 < kappa)
    (hdelta : 0 < delta) (r beta : ℝ) (hw : w ≠ 0) :
    paritySigma kappa delta r beta
        * (w / (Estimates.correctionB q r beta + paritySigma kappa delta r beta)) ^ 2
      < w ^ 2 / (Estimates.correctionB q r beta + paritySigma kappa delta r beta) := by
  have hB : 0 < Estimates.correctionB q r beta :=
    lt_of_lt_of_le hlam (correctionB_ge q r beta)
  have hs : 0 ≤ paritySigma kappa delta r beta := paritySigma_nonneg hkappa hdelta r beta
  have hBs : 0 < Estimates.correctionB q r beta + paritySigma kappa delta r beta := by
    linarith
  have heq := scalarCompletion_eq (B := Estimates.correctionB q r beta)
    (sigma := paritySigma kappa delta r beta) (w := w) hB hs
  have hres : 0 < (w - paritySigma kappa delta r beta
      * (w / (Estimates.correctionB q r beta + paritySigma kappa delta r beta))) ^ 2
      / Estimates.correctionB q r beta := by
    have hid : w - paritySigma kappa delta r beta
        * (w / (Estimates.correctionB q r beta + paritySigma kappa delta r beta))
        = Estimates.correctionB q r beta * w
            / (Estimates.correctionB q r beta + paritySigma kappa delta r beta) := by
      field_simp
      ring
    rw [hid]
    have hnum : Estimates.correctionB q r beta * w
        / (Estimates.correctionB q r beta + paritySigma kappa delta r beta) ≠ 0 := by
      refine div_ne_zero (mul_ne_zero hB.ne' hw) hBs.ne'
    have := pow_pos (abs_pos.mpr hnum) 2
    rw [sq_abs] at this
    positivity
  linarith

/-! ### The complementary region -/

private theorem pi_sq_ge_four : (4:ℝ) ≤ Real.pi ^ 2 := by
  nlinarith [Real.two_le_pi, Real.pi_pos]

theorem maxFrequency_pi_pi : Operator.maxFrequency ![Real.pi, Real.pi] = Real.pi := by
  unfold Operator.maxFrequency
  simp [abs_of_pos Real.pi_pos]

theorem theta_pi_pi : Operator.theta ![Real.pi, Real.pi] = 4 := by
  unfold Operator.theta Operator.dispersion
  simp [Fin.sum_univ_two, Real.cos_pi]
  norm_num

theorem v4LogScale_pi_pi : Frequency.v4LogScale 1 ![Real.pi, Real.pi] = 1 := by
  unfold Frequency.v4LogScale Operator.logPos
  rw [maxFrequency_pi_pi, Real.sqrt_one]
  have hle : (1:ℝ) / (1 + Real.pi) ≤ 1 := by
    rw [div_le_one (by linarith [Real.pi_pos])]
    linarith [Real.pi_pos]
  have hlog : Real.log (1 / (1 + Real.pi)) ≤ 0 :=
    Real.log_nonpos (by positivity) hle
  rw [max_eq_right hlog]
  norm_num

theorem v4Majorant_pi_pi :
    Frequency.v4Majorant 1 ![Real.pi, Real.pi] = 1 / (1 + Real.pi ^ 2) := by
  unfold Frequency.v4Majorant
  rw [maxFrequency_pi_pi, v4LogScale_pi_pi, Real.one_rpow, mul_one]

/-- `π²/2 ≤ outerRegionConstant (1/4)`, from `1 ≤ (1 + 4 log 4)^{3/2}`. -/
theorem pi_sq_half_le_outerRegionConstant :
    Real.pi ^ 2 / 2 ≤ Frequency.outerRegionConstant (1 / 4) := by
  have hlog : (0:ℝ) ≤ Real.log (1 / (1 / 4 : ℝ)) := by
    rw [show (1 : ℝ) / (1 / 4 : ℝ) = 4 by norm_num]
    exact Real.log_nonneg (by norm_num)
  have hL : (1:ℝ) ≤ 1 + 4 * Real.log (1 / (1 / 4 : ℝ)) := by linarith
  have hrpow : (1:ℝ) ≤ (1 + 4 * Real.log (1 / (1 / 4 : ℝ))) ^ (3 / 2 : ℝ) :=
    Frequency.one_le_rpow_three_halves hL
  have hge : Real.pi ^ 2 / 2
      ≤ (1 + 4 * Real.log (1 / (1 / 4 : ℝ))) ^ (3 / 2 : ℝ) * Real.pi ^ 2 / 2 := by
    nlinarith [hrpow, Real.pi_pos, sq_nonneg Real.pi]
  exact le_trans hge (le_max_right _ _)

/-- **`driftlessMajorant_le_v4Majorant` is strict**, at `λ = 1`, `r₀ = 1/4`,
`p = (π, π)`: the two sides are `1/5` and `outerRegionConstant(1/4)/(1 + π²)`,
and the second is at least `(π²/2)/(1 + π²) > 1/5`. -/
theorem strict_driftlessMajorant_le_v4Majorant :
    Operator.driftlessMajorant 1 ![Real.pi, Real.pi]
      < Frequency.outerRegionConstant (1 / 4)
          * Frequency.v4Majorant 1 ![Real.pi, Real.pi] := by
  have hpi := pi_sq_ge_four
  have hdrift : Operator.driftlessMajorant 1 ![Real.pi, Real.pi] = 1 / 5 := by
    unfold Operator.driftlessMajorant
    rw [theta_pi_pi]
    norm_num
  have hden : (0:ℝ) < 1 + Real.pi ^ 2 := by positivity
  have hK := pi_sq_half_le_outerRegionConstant
  rw [hdrift, v4Majorant_pi_pi, mul_one_div, lt_div_iff₀ hden]
  nlinarith [hK, hpi]

/-- The hypotheses of `driftlessMajorant_le_v4Majorant` hold at those data. -/
theorem nonvacuity_driftlessMajorant_le_v4Majorant :
    (0:ℝ) < 1 / 4 ∧ (1 / 4 : ℝ) ≤ 1 / 4 ∧ (0:ℝ) < 1
      ∧ |(![Real.pi, Real.pi] : Fin 2 → ℝ) 0| ≤ Real.pi
      ∧ |(![Real.pi, Real.pi] : Fin 2 → ℝ) 1| ≤ Real.pi
      ∧ (1 / 4 : ℝ) ^ 4 < Real.sqrt 1 + Operator.maxFrequency ![Real.pi, Real.pi] := by
  refine ⟨by norm_num, le_rfl, by norm_num, ?_, ?_, ?_⟩
  · simp [abs_of_pos Real.pi_pos]
  · simp [abs_of_pos Real.pi_pos]
  · rw [maxFrequency_pi_pi, Real.sqrt_one]
    nlinarith [Real.two_le_pi]

/-! ### The composed competitor cost -/

/-- The test profile of  is not the zero function: it is `1` at
`r = 1/5 ∈ Γ_{1/100}`, where the effective weight is strictly positive.  So the
right-hand side of `v4_competitor_cost_le` is not forced to vanish. -/
theorem testPhi_nondegenerate :
    Energy.testPhi (1 / 100 : ℝ) (1 / 4 : ℝ) (1 / 5) = 1
      ∧ 0 < Energy.effectiveWeight (1 / 5)
          * Energy.testPhi (1 / 100 : ℝ) (1 / 4 : ℝ) (1 / 5) ^ 2 := by
  have hmem := Energy.gammaDelta_nonempty
  have h1 : Energy.testPhi (1 / 100 : ℝ) (1 / 4 : ℝ) (1 / 5) = 1 :=
    Energy.testPhi_eq_one hmem
  refine ⟨h1, ?_⟩
  rw [h1, one_pow, mul_one]
  refine Energy.effectiveWeight_pos ?_ ?_
  · rw [abs_of_pos (by norm_num : (0:ℝ) < 1 / 5)]; norm_num
  · rw [abs_of_pos (by norm_num : (0:ℝ) < 1 / 5)]; norm_num

/-- **Every hypothesis of `v4_competitor_cost_le` is satisfiable simultaneously**
at `κ = 120`, `δ = 1/100`, `r₀ = 1/4`, `λ = 1/2`, `C₁ = 6`, `C₃ = 9` and
`φ = testPhi`, and the composed bound then holds with the constant
`6 + 9(π² + 60π³)`. -/
theorem nonvacuity_v4_competitor_cost_le :
    6 * Estimates.torusIntegral
        (fun r => (1 / 100 + r ^ 2) * Energy.testPhi (1 / 100 : ℝ) (1 / 4 : ℝ) r ^ 2)
      + 9 * Estimates.torusIntegral (fun beta => Estimates.torusIntegral (fun r =>
          paritySigma 120 (1 / 100) r beta
            * parityV ⟨1 / 2, 40, 1 / 10⟩ 120 (1 / 100)
                (fun r' _ => Real.sin r'
                  * Energy.testPhi (1 / 100 : ℝ) (1 / 4 : ℝ) r') r beta ^ 2))
      ≤ (6 + 9 * (Real.pi ^ 2 + Real.pi ^ 3 * 120 / 2))
          * Estimates.torusIntegral (fun r => Energy.effectiveWeight r
              * Energy.testPhi (1 / 100 : ℝ) (1 / 4 : ℝ) r ^ 2) := by
  have hbound : ∀ r : ℝ, |Energy.testPhi (1 / 100 : ℝ) (1 / 4 : ℝ) r| ≤ 1 := by
    intro r
    by_cases hmem : Real.sqrt (1 / 100 : ℝ) ≤ |r| ∧ |r| ≤ (1 / 4 : ℝ)
    · rw [Energy.testPhi_eq_one hmem]; norm_num
    · rw [Energy.testPhi_eq_zero hmem]; norm_num
  have h := v4_competitor_cost_le (kappa := 120) (delta := 1 / 100) (r0 := 1 / 4)
    (Kp := 1) (C1 := 6) (C3 := 9) (q := ⟨1 / 2, 40, 1 / 10⟩)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Energy.measurable_testPhi _ _) hbound
    (fun r hr => Energy.testPhi_eq_zero hr)
    (Energy.integrable_testPhi_weight (by norm_num) (by norm_num))
  linarith [h]

/-! ### The Version 4 fixed-frequency bound -/

/-- The Version 4 fixed-frequency bound is verified, unconditionally, at every
frequency of the complementary region: `V4FrequencyBound` is therefore not a
self-contradictory hypothesis, and the only region where it is still open is the
improvement region `√λ + a(p) ≤ r₀⁴`. -/
theorem v4FrequencyBound_outer_verified {lambda : ℝ} (hlambda : 0 < lambda)
    (p : Fin 2 → ℝ) (hp0 : p 0 ∈ Estimates.torus) (hp1 : p 1 ∈ Estimates.torus)
    (hbig : (1 / 4 : ℝ) ^ 4 < Real.sqrt lambda + Operator.maxFrequency p) :
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).resolventQuadratic
        hlambda (Manhattan.walshL2 ∅)
      ≤ Frequency.outerRegionConstant (1 / 4) * Frequency.v4Majorant lambda p :=
  Frequency.resolventQuadratic_le_v4Majorant_outer (by norm_num) le_rfl hlambda
    hp0 hp1 hbig

/-- The Version 4 majorant is a genuine positive real at every frequency, so no
side of the composed chain can be a junk value. -/
theorem v4Majorant_nondegenerate {lambda : ℝ} (hlambda : 0 < lambda) (p : Fin 2 → ℝ) :
    0 < Frequency.v4Majorant lambda p := Frequency.v4Majorant_pos hlambda p

/-- The uniform Green bound produced by `V4FrequencyBound C` is the explicit
finite number `17 C + 8 π² C`. -/
theorem v4_uniform_constant (C : ℝ) :
    C + 2 * (8 * C) + C * (2 * Real.pi ^ 2 / (1 / 2 : ℝ) ^ 2) = 17 * C + 8 * Real.pi ^ 2 * C := by
  ring

end Manhattan.V4
