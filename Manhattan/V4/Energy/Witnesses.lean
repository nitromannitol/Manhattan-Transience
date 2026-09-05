import Manhattan.V4.Energy.Move1

/-!
# Version 4, Move 1: anti-vacuity witnesses

Every theorem of this part is an inequality with hypotheses.  The declarations
below are the record that those hypothesis sets are **jointly satisfiable with a
nonzero test function**, so that none of the Move 1 statements is vacuously true,
and that the inequalities are strict in at least one concrete instance, so that
the two sides are not the same term after unfolding.

* `nonvacuity_betaIntegral_le`: `σ(β) = c β² log(1/|r|)` meets every hypothesis
  of `betaIntegral_le` for arbitrary `λ, c > 0` and `0 < |r| ≤ 1/4`.
* `nonvacuity_sigma_inner_lower`: `δ = ρ²` and `J` equal to its own lower bound
  meet every hypothesis of `sigma_inner_lower`.
* `nonvacuity_move1_integrand_le`, `nonvacuity_move1_energy_le`: the extremal
  density `J(r) = C₂/(|r|√(log(1/|r|)))` and the indicator `testPhi` of `Γ_δ`
  meet every hypothesis of `move1_integrand_le` and `move1_energy_le`; `testPhi`
  is not the zero function, since `gammaDelta_nonempty` exhibits a point of
  `Γ_{1/100}` inside `{|r| ≤ 1/4}`.
* `strict_add_sq_lt_effectiveWeight`: `δ + r² < q(r)` strictly at
  `δ = 1/100`, `r = 1/5`, so `add_sq_le_effectiveWeight` is not an identity in
  disguise.

Junk values are recorded rather than hidden.  `effectiveWeight 0 = 0` because
`1/0 = 0`, `log 0 = 0` and `0/0 = 0` in Lean; every statement about it therefore
carries `0 < |r|`, except `effectiveWeight_nonneg` and `measurable_effectiveWeight`.
In `move1_energy_le` the majorant is evaluated at every `r`, but the support
hypothesis makes it appear only against `φ(r)² = 0` off `Γ_δ`.
-/

open MeasureTheory

namespace Manhattan.V4.Energy

/-! ## The `β` integral -/

/-- **Anti-vacuity witness for `betaIntegral_le` (and hence for
`torusIntegral_inv_le`).**  The hypotheses hold for `σ(β) = c β² log(1/|r|)`. -/
theorem nonvacuity_betaIntegral_le {lambda c r : ℝ}
    (hlam : 0 < lambda) (hc : 0 < c) (hr : 0 < |r|) (hr1 : |r| ≤ 1 / 4) :
    Manhattan.Estimates.torusIntegral (fun b =>
        (lambda + Manhattan.Estimates.dispersion r + Manhattan.Estimates.dispersion b
          + c * (b ^ 2 * Real.log (1 / |r|)))⁻¹)
      ≤ (Real.pi ^ 2 + 1 / c) / (|r| * Real.sqrt (Real.log (1 / |r|))) := by
  refine betaIntegral_le ?_ ?_ hlam hc hr hr1 (fun b _ => le_refl _)
  · exact measurable_const.mul ((measurable_id.pow_const 2).mul measurable_const)
  · intro b
    have hL := log_inv_pos hr hr1
    positivity

/-- **Anti-vacuity witness for `sigma_inner_lower`.** -/
theorem nonvacuity_sigma_inner_lower {kappa rho beta : ℝ}
    (hkappa : 0 < kappa) (hrho : 0 < rho) (hrho' : rho ≤ 1 / 4)
    (hb : |beta| ≤ Real.sqrt rho) :
    2 / (Real.pi ^ 3 * kappa) * (beta ^ 2 * Real.log (1 / rho))
      ≤ Real.sin beta ^ 2 *
        ((kappa * Real.pi)⁻¹ * Real.log (1 + Real.pi / (rho ^ 2 + rho + |beta|))) :=
  sigma_inner_lower hkappa (by positivity) le_rfl hrho hrho' hb le_rfl

/-! ## The effective weight -/

/-- `Γ_{1/100} ∩ {|r| ≤ 1/4}` is nonempty: it contains `1/5`. -/
theorem gammaDelta_nonempty :
    Real.sqrt (1 / 100 : ℝ) ≤ |(1 / 5 : ℝ)| ∧ |(1 / 5 : ℝ)| ≤ 1 / 4 := by
  constructor
  · rw [show (1 / 100 : ℝ) = (1 / 10) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [abs_of_pos (by norm_num : (0:ℝ) < 1 / 5)]
    norm_num
  · rw [abs_of_pos (by norm_num : (0:ℝ) < 1 / 5)]
    norm_num

/-- **`add_sq_le_effectiveWeight` is not an identity**: at `δ = 1/100`, `r = 1/5`
the inequality `δ + r² ≤ q(r)` is strict, because `log 5 < 2`. -/
theorem strict_add_sq_lt_effectiveWeight :
    (1 / 100 : ℝ) + (1 / 5 : ℝ) ^ 2 < effectiveWeight (1 / 5) := by
  have h5 : |(1 / 5 : ℝ)| = 1 / 5 := abs_of_pos (by norm_num)
  have he : (5 : ℝ) < Real.exp 2 := by
    have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos 1]
  have hlt : Real.log 5 < 2 := by
    have h := Real.log_lt_log (by norm_num : (0:ℝ) < 5) he
    rwa [Real.log_exp] at h
  have h0 : 0 < Real.log 5 := Real.log_pos (by norm_num)
  have hsq : Real.sqrt (Real.log 5) < 2 := by
    nlinarith [Real.sq_sqrt h0.le, Real.sqrt_nonneg (Real.log 5)]
  unfold effectiveWeight
  rw [h5, show (1:ℝ) / (1 / 5) = 5 by norm_num,
    lt_div_iff₀ (Real.sqrt_pos.mpr h0)]
  nlinarith [hsq, Real.sqrt_nonneg (Real.log 5)]

/-! ## Move 1 -/

/-- **Anti-vacuity witness for `move1_integrand_le`**: the extremal density
`J = C₂/(|r| √(log(1/|r|)))` meets its hypothesis with equality. -/
theorem nonvacuity_move1_integrand_le {delta C1 C2 r : ℝ} (phi : ℝ → ℝ)
    (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hd : 0 ≤ delta)
    (hdr : Real.sqrt delta ≤ |r|) (hr : 0 < |r|) (hr1 : |r| ≤ 1 / 4) :
    C1 * ((delta + r ^ 2) * phi r ^ 2)
        + Real.sin r ^ 2 * (C2 / (|r| * Real.sqrt (Real.log (1 / |r|)))) * phi r ^ 2
      ≤ (C1 + C2) * (effectiveWeight r * phi r ^ 2) :=
  move1_integrand_le phi hC1 hC2 hd hdr hr hr1 le_rfl

/-- The test profile: the indicator of `Γ_δ = {√δ ≤ |r| ≤ r₀}`.  It is not the
zero function whenever `Γ_δ` is nonempty, which `gammaDelta_nonempty` exhibits. -/
noncomputable def testPhi (delta r0 : ℝ) : ℝ → ℝ :=
  Set.indicator {r : ℝ | Real.sqrt delta ≤ |r| ∧ |r| ≤ r0} (fun _ => (1 : ℝ))

theorem measurableSet_gammaDelta (delta r0 : ℝ) :
    MeasurableSet {r : ℝ | Real.sqrt delta ≤ |r| ∧ |r| ≤ r0} := by
  have habs : Measurable (fun r : ℝ => |r|) := continuous_abs.measurable
  have h1 : MeasurableSet {r : ℝ | Real.sqrt delta ≤ |r|} :=
    measurableSet_le measurable_const habs
  have h2 : MeasurableSet {r : ℝ | |r| ≤ r0} :=
    measurableSet_le habs measurable_const
  exact h1.inter h2

theorem testPhi_eq_zero {delta r0 r : ℝ}
    (h : ¬ (Real.sqrt delta ≤ |r| ∧ |r| ≤ r0)) : testPhi delta r0 r = 0 := by
  unfold testPhi
  simp only [Set.indicator]
  split_ifs with hmem
  · exact absurd hmem h
  · rfl

theorem testPhi_eq_one {delta r0 r : ℝ}
    (h : Real.sqrt delta ≤ |r| ∧ |r| ≤ r0) : testPhi delta r0 r = 1 := by
  unfold testPhi
  simp only [Set.indicator]
  split_ifs with hmem
  · rfl
  · exact absurd h hmem

theorem measurable_testPhi (delta r0 : ℝ) : Measurable (testPhi delta r0) := by
  unfold testPhi
  exact measurable_const.indicator (measurableSet_gammaDelta delta r0)

/-- The majorant density of Move 1 is integrable for the test profile. -/
theorem integrable_testPhi_weight {delta r0 : ℝ} (hdpos : 0 < delta) (hr0 : r0 ≤ 1 / 4) :
    Integrable (fun r => effectiveWeight r * testPhi delta r0 r ^ 2)
      (volume.restrict Manhattan.Estimates.torus) := by
  have h_meas : Measurable (fun r => effectiveWeight r * testPhi delta r0 r ^ 2) :=
    measurable_effectiveWeight.mul ((measurable_testPhi delta r0).pow_const 2)
  have h_bound : ∀ x, |effectiveWeight x * testPhi delta r0 x ^ 2| ≤ (1 / 4 : ℝ) := fun x => by
    by_cases hx : Real.sqrt delta ≤ |x| ∧ |x| ≤ r0
    · rw [testPhi_eq_one hx, one_pow, mul_one]
      have h_x_pos : 0 < |x| := lt_of_lt_of_le (Real.sqrt_pos.mpr hdpos) hx.1
      have h_x_bound : |x| ≤ 1 / 4 := le_trans hx.2 hr0
      have h_eff : effectiveWeight x ≤ |x| := effectiveWeight_le_abs h_x_pos h_x_bound
      rw [abs_of_nonneg (effectiveWeight_nonneg x)]
      linarith
    · rw [testPhi_eq_zero hx]
      norm_num
  exact Manhattan.Estimates.integrableOn_torus_of_bounded h_meas h_bound

/-- The competitor energy density is integrable for the test profile, so the
left-hand side of `nonvacuity_move1_energy_le` is a genuine Bochner integral and
not the junk value `0`. -/
theorem integrable_testPhi_density {delta C1 C2 r0 : ℝ}
    (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hdpos : 0 < delta) (hr0 : r0 ≤ 1 / 4) :
    Integrable (fun r => C1 * ((delta + r ^ 2) * testPhi delta r0 r ^ 2)
        + Real.sin r ^ 2 * (C2 / (|r| * Real.sqrt (Real.log (1 / |r|))))
            * testPhi delta r0 r ^ 2)
      (volume.restrict Manhattan.Estimates.torus) := by
  have hsqrtpos : 0 < Real.sqrt delta := Real.sqrt_pos.mpr hdpos
  refine integrable_move1_density (delta := delta) (C1 := C1) (r0 := r0)
    (Kp := 1) (Kj := C2 / Real.sqrt delta) _ _
    (measurable_testPhi delta r0)
    (measurable_const.div ((continuous_abs.measurable).mul
      (Real.continuous_sqrt.measurable.comp
        (Real.measurable_log.comp (measurable_const.div continuous_abs.measurable)))))
    (fun r h => testPhi_eq_zero h) hr0 hdpos.le hC1 zero_le_one
    (by positivity) ?_ ?_
  · intro r hr hrr0
    rw [testPhi_eq_one ⟨hr, hrr0⟩]
    norm_num
  · intro r hr hrr0
    have hrpos : 0 < |r| := lt_of_lt_of_le hsqrtpos hr
    have hr1 : |r| ≤ 1 / 4 := le_trans hrr0 hr0
    have hS : 1 ≤ Real.sqrt (Real.log (1 / |r|)) := by
      have h1 : Real.sqrt 1 ≤ Real.sqrt (Real.log (1 / |r|)) :=
        Real.sqrt_le_sqrt (one_lt_log_inv hrpos hr1).le
      simpa using h1
    have hden : Real.sqrt delta ≤ |r| * Real.sqrt (Real.log (1 / |r|)) := by nlinarith
    rw [abs_of_nonneg (by positivity)]
    exact div_le_div_of_nonneg_left hC2 hsqrtpos hden

/-- **Anti-vacuity witness for `move1_energy_le`**: with the nonzero test profile
`testPhi` and the extremal density `J(r) = C₂/(|r| √(log(1/|r|)))` every
hypothesis holds. -/
theorem nonvacuity_move1_energy_le {delta C1 C2 r0 : ℝ}
    (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hdpos : 0 < delta) (hr0 : r0 ≤ 1 / 4) :
    Manhattan.Estimates.torusIntegral
        (fun r => C1 * ((delta + r ^ 2) * testPhi delta r0 r ^ 2)
          + Real.sin r ^ 2 * (C2 / (|r| * Real.sqrt (Real.log (1 / |r|))))
              * testPhi delta r0 r ^ 2)
      ≤ (C1 + C2) * Manhattan.Estimates.torusIntegral
        (fun r => effectiveWeight r * testPhi delta r0 r ^ 2) :=
  move1_energy_le (testPhi delta r0)
    (fun r => C2 / (|r| * Real.sqrt (Real.log (1 / |r|))))
    hC1 hC2 hdpos hr0 (fun r h => testPhi_eq_zero h)
    (fun _ _ _ => le_refl _) (fun _ => by positivity)
    (integrable_testPhi_weight hdpos hr0)

/-- **Anti-vacuity witness for `effectiveEnergy_le`**: taking `r_λ` equal to the
right-hand side of the competitor bound makes `hcompetitor` hold, so the whole
hypothesis set of `effectiveEnergy_le` is satisfiable with a nonzero `φ`. -/
theorem nonvacuity_effectiveEnergy_le {delta C1 C2 r0 h0 s : ℝ}
    (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hdpos : 0 < delta) (hr0 : r0 ≤ 1 / 4) :
    (1 - s * Manhattan.Estimates.torusIntegral (testPhi delta r0)) ^ 2 / h0
        + Manhattan.Estimates.torusIntegral
            (fun r => C1 * ((delta + r ^ 2) * testPhi delta r0 r ^ 2)
              + Real.sin r ^ 2 * (C2 / (|r| * Real.sqrt (Real.log (1 / |r|))))
                  * testPhi delta r0 r ^ 2)
      ≤ (1 - s * Manhattan.Estimates.torusIntegral (testPhi delta r0)) ^ 2 / h0
        + (C1 + C2) * Manhattan.Estimates.torusIntegral
            (fun r => effectiveWeight r * testPhi delta r0 r ^ 2) :=
  effectiveEnergy_le (testPhi delta r0)
    (fun r => C2 / (|r| * Real.sqrt (Real.log (1 / |r|))))
    hC1 hC2 hdpos hr0 (fun r h => testPhi_eq_zero h)
    (fun _ _ _ => le_refl _) (fun _ => by positivity)
    (integrable_testPhi_weight hdpos hr0) (le_refl _)

end Manhattan.V4.Energy
