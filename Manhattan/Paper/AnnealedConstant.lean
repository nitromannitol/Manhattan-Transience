import Manhattan.Paper.FrequencyBound

/-!
# `thm:annealed` with the constant `2048`

`thm:annealed` (`paper/arxiv/main.tex:180-188`, proof at `:1094-1121`): for every
`λ ∈ (0,1]`, `∫₀^∞ e^{-λt} p̄_t(0,0) dt ≤ 2048`, and `∫₀^∞ p̄_t(0,0) dt ≤ 2048`.

The proof integrates three bounds on `r_λ(p)`, each a function of `a(p)` alone
(`greenRadial`): `1/λ` on `a(p) ≤ √λ`; `prop:frequency` with
`[1 + log₊(1/(√λ + a))] ≥ [1 + log(1/a)]/2` on `√λ < a(p) < 1/4`; and
`π²/(2a(p)²)` on `a(p) ≥ 1/4` (`concreteGreenDensity_le_greenRadial`).  The
square `{a(p) ≤ b}` has normalized measure `b²/π²`, so a function of `a(p)`
integrates to `(2/π²) ∫₀^π b φ(b) db` (`normalizedFrequencyIntegral_le_radial`,
stated as an upper bound).  The three pieces give
`1/π² + 2^{7/2}·2048/(π²√(1 + log 4)) + log(4π) < 2048`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal
open Manhattan Manhattan.V4.Frequency Manhattan.Estimates

namespace Manhattan.Paper

noncomputable section

/-! ### The radial majorant -/

/-- `2048 · 2^{3/2}`. -/
def middleConstant : ℝ := 2048 * (2 * Real.sqrt 2)

theorem middleConstant_pos : 0 < middleConstant := by
  unfold middleConstant
  positivity

/-- The bound on `r_λ(p)` as a function of `b = a(p)`. -/
def greenRadial (lambda b : ℝ) : ℝ :=
  if b ≤ Real.sqrt lambda then lambda⁻¹
  else if b < 1 / 4 then middleConstant * annulusKernel b / b
  else Real.pi ^ 2 / (2 * b ^ 2)

theorem maxFrequency_concreteFrequency (z : ℝ × ℝ) :
    Operator.maxFrequency (Manhattan.Glue.concreteFrequency z) = squareRadius z := by
  simp [Operator.maxFrequency, Manhattan.Glue.concreteFrequency, squareRadius]

/-- On `√λ < a < 1/4`: `1 + log₊(1/(√λ + a)) ≥ (1 + log(1/a))/2`. -/
theorem half_le_v4LogScale {lambda : ℝ} (hlambda : 0 < lambda) {p : Fin 2 → ℝ}
    (hlow : Real.sqrt lambda < Operator.maxFrequency p)
    (hhigh : Operator.maxFrequency p < 1 / 4) :
    (1 - Real.log (Operator.maxFrequency p)) / 2 ≤ v4LogScale lambda p := by
  set a := Operator.maxFrequency p with ha
  have hs := Real.sqrt_pos.2 hlambda
  have hapos : 0 < a := hs.trans hlow
  have hsum : Real.sqrt lambda + a ≤ 2 * a := by linarith
  have hlog1 : Real.log (1 / (Real.sqrt lambda + a)) ≥ -Real.log (2 * a) := by
    rw [one_div, Real.log_inv]
    exact neg_le_neg (Real.log_le_log (by positivity) hsum)
  have hlog2 : Real.log (2 * a) = Real.log 2 + Real.log a :=
    Real.log_mul (by norm_num) hapos.ne'
  have hloga : Real.log a < Real.log (1 / 4) := Real.log_lt_log hapos hhigh
  have hlog4 : Real.log (1 / 4 : ℝ) = -(2 * Real.log 2) := by
    rw [one_div, Real.log_inv, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  have hpos : Operator.logPos (1 / (Real.sqrt lambda + a)) ≥
      Real.log (1 / (Real.sqrt lambda + a)) := le_max_left _ _
  unfold v4LogScale
  rw [← ha]
  linarith

/-- **The three bounds of the proof of `thm:annealed`.** -/
theorem concreteGreenDensity_le_greenRadial {lambda : ℝ} (hlambda : 0 < lambda)
    (hlambda1 : lambda ≤ 1) {z : ℝ × ℝ} (hz1 : z.1 ∈ torus) (hz2 : z.2 ∈ torus) :
    Manhattan.Glue.concreteGreenDensity lambda z ≤ greenRadial lambda (squareRadius z) := by
  set p := Manhattan.Glue.concreteFrequency z with hp
  have hmax : Operator.maxFrequency p = squareRadius z := maxFrequency_concreteFrequency z
  rw [Manhattan.Glue.concreteGreenDensity_eq_resolventQuadratic hlambda z]
  have hdrift := Manhattan.Glue.concrete_resolventQuadratic_le_driftless hlambda p
  have hth := Manhattan.operatorTheta_nonneg p
  have hden : 0 < lambda + Operator.theta p := by linarith
  set b := squareRadius z with hb
  have hp0 : |p 0| ≤ Real.pi := abs_le.2 ⟨hz1.1.le, hz1.2⟩
  have hp1 : |p 1| ≤ Real.pi := abs_le.2 ⟨hz2.1.le, hz2.2⟩
  unfold greenRadial
  split_ifs with h1 h2
  · refine hdrift.trans ?_
    rw [Operator.driftlessMajorant, one_div]
    exact inv_anti₀ hlambda (by linarith)
  · -- the middle region, from `prop:frequency`
    have hs := Real.sqrt_pos.2 hlambda
    have hlow : Real.sqrt lambda < Operator.maxFrequency p := by rw [hmax]; exact lt_of_not_ge h1
    have hhigh : Operator.maxFrequency p < 1 / 4 := by rw [hmax]; exact h2
    have hbpos : 0 < b := by rw [← hmax]; exact hs.trans hlow
    have hfreq := frequencyBound_2048 lambda hlambda hlambda1 p hz1 hz2
    have hL := half_le_v4LogScale hlambda hlow hhigh
    rw [hmax] at hL
    set L := v4LogScale lambda p with hLdef
    set m := (1 - Real.log b) / 2 with hm
    have hlogb : Real.log b < 0 := Real.log_neg hbpos (by linarith)
    have hm0 : 0 < m := by rw [hm]; linarith
    have hL0 : 0 ≤ L := hm0.le.trans hL
    have hpow : m * Real.sqrt m ≤ L ^ (3 / 2 : ℝ) := by
      rw [rpow_three_halves hL0]
      exact mul_le_mul hL (Real.sqrt_le_sqrt hL) (Real.sqrt_nonneg _) hL0
    set A := Real.sqrt (1 - Real.log b) with hA
    have hA0 : 0 < A := Real.sqrt_pos.2 (by linarith)
    have hAm : A ^ 3 = 2 * Real.sqrt 2 * (m * Real.sqrt m) := by
      have h2m : 1 - Real.log b = 2 * m := by rw [hm]; ring
      rw [hA, h2m, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2) m]
      have hs2 := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
      have hsm := Real.sq_sqrt hm0.le
      ring_nf
      rw [show Real.sqrt 2 ^ 3 = Real.sqrt 2 ^ 2 * Real.sqrt 2 by ring, hs2,
        show Real.sqrt m ^ 3 = Real.sqrt m ^ 2 * Real.sqrt m by ring, hsm]
      ring
    have hmaj : v4Majorant lambda p ≤ 1 / (b ^ 2 * (m * Real.sqrt m)) := by
      rw [v4Majorant, hmax]
      have hq : 0 < b ^ 2 * (m * Real.sqrt m) := by positivity
      refine one_div_le_one_div_of_le hq ?_
      have := mul_le_mul_of_nonneg_left hpow (sq_nonneg b)
      linarith
    refine hfreq.trans ?_
    have hq : 0 < b ^ 2 * (m * Real.sqrt m) := by positivity
    have hgoal : 2048 * (1 / (b ^ 2 * (m * Real.sqrt m))) =
        middleConstant * annulusKernel b / b := by
      rw [middleConstant, annulusKernel, ← hA]
      have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
      rw [hAm]
      field_simp
    rw [← hgoal]
    exact mul_le_mul_of_nonneg_left hmaj (by norm_num)
  · -- the outer region, from the zero function
    have hb4 : 1 / 4 ≤ b := le_of_not_gt h2
    have hbpos : 0 < b := by linarith
    have hthb : 2 * b ^ 2 / Real.pi ^ 2 ≤ Operator.theta p := by
      have hd0 := V4.Energy.two_sq_div_pi_sq_le_dispersion hp0
      have hd1 := V4.Energy.two_sq_div_pi_sq_le_dispersion hp1
      have hn0 : 0 ≤ Estimates.dispersion (p 0) := Estimates.dispersion_nonneg _
      have hn1 : 0 ≤ Estimates.dispersion (p 1) := Estimates.dispersion_nonneg _
      have htheta : Operator.theta p = Estimates.dispersion (p 0) + Estimates.dispersion (p 1) := by
        rw [Operator.theta, Fin.sum_univ_two]
        rfl
      rw [htheta]
      have hbmax : b = max |p 0| |p 1| := by rw [← hmax]; rfl
      rcases le_total |p 1| |p 0| with h | h
      · rw [max_eq_left h] at hbmax
        rw [hbmax, sq_abs]
        linarith
      · rw [max_eq_right h] at hbmax
        rw [hbmax, sq_abs]
        linarith
    refine hdrift.trans ?_
    rw [Operator.driftlessMajorant, one_div]
    have hq : 0 < 2 * b ^ 2 / Real.pi ^ 2 := by positivity
    calc (lambda + Operator.theta p)⁻¹ ≤ (2 * b ^ 2 / Real.pi ^ 2)⁻¹ :=
          inv_anti₀ hq (by linarith)
      _ = Real.pi ^ 2 / (2 * b ^ 2) := by rw [inv_div]

end

end Manhattan.Paper
