import Manhattan.V4.Move2Supply

/-!
# The paper's constant, part 1: tightening Move 3

`results/01-transience/manuscript.tex` asserts the explicit Green bound
`∫₀^∞ p̄_t(0,0) dt ≤ 2048` (`eq:green-explicit`), proved from the
fixed-frequency bound `prop:frequency` with `C = 2048`.  The Version 4 Lean
chain proves the same two statements with much larger constants.  This file
removes the part of the discrepancy that is a pure loss in the scalar
arithmetic of Move 3; the rest is analysed in
`Manhattan/Paper/Constant/GreenConstant.lean` and in
.

Two steps are tightened, both downstream of `Manhattan.V4.v4Constant`, and
neither touches `Manhattan/V4/`.

* `five_le_negLog`.  On the improvement region `δ ≤ r₀⁴ ≤ 4⁻⁴` the logarithmic
  scale `L = log(1/δ)` is at least `4 log 4 = 8 log 2 > 5.54`, not merely `1`,
  which is all `Manhattan.V4.Frequency.one_le_negLog` extracts.

* `rpow_le_Zdelta_tight`.  With `L ≥ 5` the manuscript's step
  `1 + L ≤ (6/5) L`, `(6/5)^{3/2} < 3/2` replaces `1 + L ≤ 2 L`, and the
  comparison constant of `Manhattan.V4.Frequency.rpow_le_Zdelta` drops from
  `30π ≈ 94.25` to `9√2π < 40`.

* `move3_bound_tight`.  Consequently the fixed-frequency constant of
  `Manhattan.V4.Frequency.move3_bound` drops from `8π³ C ≈ 248.05 C` to
  `10π² C ≈ 98.70 C`.  For comparison, the manuscript's own optimized value is
  `(9√2/4)π³ C = 98.66 C`, so after this step Move 3 is within `0.04%` of the
  paper.

Nothing here is a new mathematical idea: `rpow_le_Zdelta_tight` is exactly the
manuscript's own estimate at `eq:frequency-bound`, carried out at the
improvement region's true logarithm.
-/

noncomputable section

namespace Manhattan.Paper.Constant

open Manhattan.V4 Manhattan.V4.Frequency

/-- On the improvement region `δ ≤ r₀⁴`, `r₀ ≤ 1/4`, the logarithmic scale
`L = log(1/δ)` is at least `5`.  `Manhattan.V4.Frequency.one_le_negLog`
extracts only `1` from the same hypotheses. -/
theorem five_le_negLog {r0 delta : ℝ} (hr0 : 0 < r0) (hr01 : r0 ≤ 1 / 4)
    (hd : 0 < delta) (hdle : delta ≤ r0 ^ 4) : 5 ≤ -Real.log delta := by
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hr0log : Real.log r0 ≤ Real.log (1 / 4) := Real.log_le_log hr0 hr01
  have hquarter : Real.log (1 / 4 : ℝ) = -(2 * Real.log 2) := by
    rw [one_div, Real.log_inv, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  have hdlog : Real.log delta ≤ Real.log (r0 ^ 4) := Real.log_le_log hd hdle
  rw [Real.log_pow] at hdlog
  push_cast at hdlog
  rw [hquarter] at hr0log
  linarith

theorem sqrt_two_lt : Real.sqrt 2 < 1.41422 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]

/-- **The tightened comparison of the logarithmic scale with `Z_δ`.**
`Manhattan.V4.Frequency.rpow_le_Zdelta` proves the same statement with `30π`
in place of `40`; the improvement is the manuscript's `1 + L ≤ (6/5)L` in
place of `1 + L ≤ 2L`, available because `L ≥ 5` on the improvement region. -/
theorem rpow_le_Zdelta_tight {r0 delta : ℝ} (hr0 : 0 < r0) (hr01 : r0 ≤ 1 / 4)
    (hd : 0 < delta) (hdle : delta ≤ r0 ^ 4) :
    (1 + -Real.log delta) ^ (3 / 2 : ℝ) ≤ 40 * Zdelta r0 delta := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hpilt : Real.pi < 3.141593 := Real.pi_lt_d6
  have hs2 : Real.sqrt 2 < 1.41422 := sqrt_two_lt
  have hs2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  set L := -Real.log delta with hLdef
  have hL : (5:ℝ) ≤ L := five_le_negLog hr0 hr01 hd hdle
  have hLpos : 0 < L := by linarith
  have hZpos : 0 < Zdelta r0 delta := Zdelta_pos hr0 hr01 hd hdle
  have h1 : (1 + L) ^ (3 / 2 : ℝ) ≤ ((6/5) * L) ^ (3 / 2 : ℝ) :=
    rpow_three_halves_mono (by linarith) (by linarith)
  have h2 : ((6/5) * L) ^ (3 / 2 : ℝ) = (6/5) * L * Real.sqrt ((6/5) * L) :=
    rpow_three_halves (by linarith)
  have hsqrtmul : Real.sqrt ((6/5) * L) = Real.sqrt (6/5) * Real.sqrt L :=
    Real.sqrt_mul (by norm_num) L
  have hsq65 : Real.sqrt (6/5 : ℝ) ≤ 5/4 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 6/5), Real.sqrt_nonneg (6/5 : ℝ)]
  have h4 : (6/5) * L * Real.sqrt ((6/5) * L) ≤ (3/2) * (L * Real.sqrt L) := by
    rw [hsqrtmul]
    nlinarith [mul_nonneg (mul_nonneg hLpos.le (Real.sqrt_nonneg L)) (sub_nonneg.2 hsq65)]
  have h5 : L * Real.sqrt L / (6 * Real.sqrt 2 * Real.pi) ≤ Zdelta r0 delta :=
    (Zdelta_bounds hr0 hr01 hd hdle).1
  have hden : (0:ℝ) < 6 * Real.sqrt 2 * Real.pi := by positivity
  have h6 : L * Real.sqrt L ≤ 6 * Real.sqrt 2 * Real.pi * Zdelta r0 delta := by
    rw [div_le_iff₀ hden] at h5
    linarith
  have h7 : 9 * Real.sqrt 2 * Real.pi ≤ 40 := by nlinarith [hs2, hpilt, hs2pos, hpi]
  calc (1 + L) ^ (3 / 2 : ℝ) ≤ ((6/5) * L) ^ (3 / 2 : ℝ) := h1
    _ = (6/5) * L * Real.sqrt ((6/5) * L) := h2
    _ ≤ (3/2) * (L * Real.sqrt L) := h4
    _ ≤ (3/2) * (6 * Real.sqrt 2 * Real.pi * Zdelta r0 delta) := by linarith
    _ = (9 * Real.sqrt 2 * Real.pi) * Zdelta r0 delta := by ring
    _ ≤ 40 * Zdelta r0 delta := by nlinarith [hZpos, h7]

/-! ### Move 3 -/

/-- The scalar core of Move 3, on opaque reals: `A` is `a(p)² Λ^{3/2}`, `B` is
`s² Z_δ / C`, and `K` is the composed constant. -/
private theorem scalar_move3 {rl lambda th A B K Cc : ℝ}
    (hlambda : 0 < lambda) (hth : 0 ≤ th) (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hK1 : 1 ≤ K) (hKC : 10 * Real.pi ^ 2 * Cc ≤ K)
    (hlow : A ≤ 10 * Real.pi ^ 2 * Cc * B)
    (hrl : rl ≤ 1 / (lambda + th + B)) :
    rl ≤ K * (1 / (lambda + A)) := by
  have hD : 0 < lambda + th + B := by linarith
  have hE : 0 < lambda + A := by linarith
  have hkey : lambda + A ≤ K * (lambda + th + B) := by
    have h1 : lambda ≤ K * lambda := le_mul_of_one_le_left hlambda.le hK1
    have h2 : 0 ≤ K * th := mul_nonneg (by linarith) hth
    have h3 : 10 * Real.pi ^ 2 * Cc * B ≤ K * B := by nlinarith
    nlinarith
  refine hrl.trans ?_
  rw [mul_one_div, div_le_div_iff₀ hD hE]
  linarith

/-- **MOVE 3, tightened.**  The statement of
`Manhattan.V4.Frequency.move3_bound` with `8π³ C` replaced by `10π² C`. -/
theorem move3_bound_tight {r0 lambda rl s C : ℝ} {p : Fin 2 → ℝ}
    (hr0 : 0 < r0) (hr01 : r0 ≤ 1 / 4) (hlambda : 0 < lambda) (hC : 0 < C)
    (hs : (2 / Real.pi) ^ 2 * Operator.maxFrequency p ^ 2 ≤ s ^ 2)
    (hdle : Real.sqrt lambda + Operator.maxFrequency p ≤ r0 ^ 4)
    (hmove2 : rl ≤ 1 / (lambda + Operator.theta p
        + s ^ 2 * Zdelta r0 (Real.sqrt lambda + Operator.maxFrequency p) / C)) :
    rl ≤ max 1 (10 * Real.pi ^ 2 * C) * v4Majorant lambda p := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hanonneg : 0 ≤ Operator.maxFrequency p := maxFrequency_nonneg p
  have hdpos : 0 < Real.sqrt lambda + Operator.maxFrequency p :=
    add_pos_of_pos_of_nonneg (Real.sqrt_pos.2 hlambda) hanonneg
  have hLam1 : 1 ≤ v4LogScale lambda p ^ (3 / 2 : ℝ) := one_le_v4LogScale_rpow lambda p
  have hA : 0 ≤ Operator.maxFrequency p ^ 2 * v4LogScale lambda p ^ (3 / 2 : ℝ) := by
    positivity
  have hthetann : 0 ≤ Operator.theta p := by
    rw [Manhattan.Estimates.operator_theta_eq]
    exact Manhattan.Estimates.theta_nonneg p
  have hZpos : 0 < Zdelta r0 (Real.sqrt lambda + Operator.maxFrequency p) :=
    Zdelta_pos hr0 hr01 hdpos hdle
  have hrpow : v4LogScale lambda p ^ (3 / 2 : ℝ)
      ≤ 40 * Zdelta r0 (Real.sqrt lambda + Operator.maxFrequency p) := by
    rw [v4LogScale_eq hr0 hr01 hlambda hdle]
    exact rpow_le_Zdelta_tight hr0 hr01 hdpos hdle
  have hZlow : v4LogScale lambda p ^ (3 / 2 : ℝ) / 40
      ≤ Zdelta r0 (Real.sqrt lambda + Operator.maxFrequency p) := by linarith
  have hprod : (2 / Real.pi) ^ 2 * Operator.maxFrequency p ^ 2
        * (v4LogScale lambda p ^ (3 / 2 : ℝ) / 40)
      ≤ s ^ 2 * Zdelta r0 (Real.sqrt lambda + Operator.maxFrequency p) :=
    mul_le_mul hs hZlow (by positivity) (sq_nonneg s)
  have heq : (2 / Real.pi) ^ 2 * Operator.maxFrequency p ^ 2
        * (v4LogScale lambda p ^ (3 / 2 : ℝ) / 40)
      = (Operator.maxFrequency p ^ 2 * v4LogScale lambda p ^ (3 / 2 : ℝ))
          / (10 * Real.pi ^ 2) := by
    field_simp
    ring
  rw [heq] at hprod
  have hlow : Operator.maxFrequency p ^ 2 * v4LogScale lambda p ^ (3 / 2 : ℝ)
      ≤ 10 * Real.pi ^ 2 * C
        * (s ^ 2 * Zdelta r0 (Real.sqrt lambda + Operator.maxFrequency p) / C) := by
    have hCne : C ≠ 0 := ne_of_gt hC
    have hrw : 10 * Real.pi ^ 2 * C
        * (s ^ 2 * Zdelta r0 (Real.sqrt lambda + Operator.maxFrequency p) / C)
        = 10 * Real.pi ^ 2
            * (s ^ 2 * Zdelta r0 (Real.sqrt lambda + Operator.maxFrequency p)) := by
      field_simp
    rw [hrw]
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 10 * Real.pi ^ 2)] at hprod
    linarith
  have hB : 0 ≤ s ^ 2 * Zdelta r0 (Real.sqrt lambda + Operator.maxFrequency p) / C := by
    positivity
  have hmain := scalar_move3 (rl := rl) (lambda := lambda) (th := Operator.theta p)
    (A := Operator.maxFrequency p ^ 2 * v4LogScale lambda p ^ (3 / 2 : ℝ))
    (B := s ^ 2 * Zdelta r0 (Real.sqrt lambda + Operator.maxFrequency p) / C)
    (K := max 1 (10 * Real.pi ^ 2 * C)) (Cc := C)
    hlambda hthetann hB hA (le_max_left _ _) (le_max_right _ _) hlow hmove2
  simpa only [v4Majorant] using hmain

/-- **The tightened fixed-frequency bound.**  The statement of
`Manhattan.V4.Frequency.v4FrequencyBound_of_move2Supply` with `8π³ C` replaced
by `10π² C`; the complementary region is unchanged. -/
theorem v4FrequencyBound_tight {r0 C : ℝ}
    (hr0 : 0 < r0) (hr01 : r0 ≤ 1 / 4) (hC : 0 < C)
    (hsupply : V4Move2Supply r0 C) :
    V4FrequencyBound
      (max (max 1 (10 * Real.pi ^ 2 * C)) (outerRegionConstant r0)) := by
  intro lambda hlambda hlambda1 p hp0 hp1
  have hp0abs : |p 0| ≤ Real.pi := abs_le.2 ⟨hp0.1.le, hp0.2⟩
  have hp1abs : |p 1| ≤ Real.pi := abs_le.2 ⟨hp1.1.le, hp1.2⟩
  have hmpos : 0 ≤ v4Majorant lambda p := (v4Majorant_pos hlambda p).le
  rcases le_or_gt (Real.sqrt lambda + Operator.maxFrequency p) (r0 ^ 4) with hle | hgt
  · obtain ⟨s, hs, hmove2⟩ := hsupply lambda hlambda hlambda1 p hp0 hp1 hle
    exact (move3_bound_tight hr0 hr01 hlambda hC hs hle hmove2).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hmpos)
  · have hdrift := Manhattan.Glue.concrete_resolventQuadratic_le_driftless hlambda p
    have houter := driftlessMajorant_le_v4Majorant hr0 hr01 hlambda hp0abs hp1abs hgt
    exact (hdrift.trans houter).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hmpos)

end Manhattan.Paper.Constant
