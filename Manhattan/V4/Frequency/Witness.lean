import Manhattan.V4.Frequency.Integration
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Version 4, : non-degeneracy witnesses

Every lemma of this part is a bound of the form `X ≤ Y`, and three earlier declarations
in this repository were true but worthless (an `X ≤ X` after unfolding, a hypothesis
forcing the bounded quantity to vanish, a clause discharged because the datum passed in
was the thing being characterised). This file rules those failure modes out by machine
check rather than by inspection.

* `witness_bridge_strict`: the comparison
  `v4Majorant λ p ≤ Operator.frequencyMajorant r₀ λ p` is STRICT at the explicit
  frequency `p = (π, π)`, `λ = 1`, `r₀ = 1/4`, where the two sides are `1/(1+π²)` and
  `1/π²`. So the bridge is not an unfolding identity.
* `witness_effectiveEnergy_attained`: the Move 1 hypothesis of
  `resolvent_le_of_effectiveEnergy` is satisfiable with `rl` equal to the conclusion's
  right-hand side `1/(h₀ + s² Z_δ/C)`, which is strictly positive. So the hypothesis
  neither is empty nor forces the bounded quantity to vanish, and the conclusion is
  attained. Proving it goes through both substitution identities
  (`profile_gammaIntegral`, `energy_gammaIntegral`), so those are exercised too.
* `witness_move3_hypotheses`: the standing hypotheses of `move3_bound` -- including
  `hs`, which is the intended `s = sin p₁` fed through Jordan's inequality -- hold
  simultaneously at `r₀ = 1/4`, `λ = 10⁻⁶`, `p = (1/2000, 0)`.

Positivity of the two quantities the part bounds things by is
`Manhattan.V4.Frequency.Zdelta_pos` and `Manhattan.V4.Frequency.v4Majorant_pos`; no
integral in this part appears without either an integrability proof or an evaluation.
-/

noncomputable section

namespace Manhattan.V4.Frequency

/-- The bridge inequality is strict at `p = (π, π)`, `λ = 1`, `r₀ = 1/4`:
`1/(1 + π²) < 1/π² = Operator.frequencyMajorant (1/4) 1 (π, π)`. -/
theorem witness_bridge_strict :
    v4Majorant 1 ![Real.pi, Real.pi]
      < Operator.frequencyMajorant (1 / 4) 1 ![Real.pi, Real.pi] := by
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hpi : 0 < Real.pi := Real.pi_pos
  have hmax : Operator.maxFrequency ![Real.pi, Real.pi] = Real.pi := by
    simp [Operator.maxFrequency, abs_of_pos Real.pi_pos]
  have hlogzero : ∀ c : ℝ, 0 < c → c ≤ 1 →
      Operator.logPos (c / (1 + Real.pi)) = 0 := by
    intro c hc hc1
    have hlt : Real.log (c / (1 + Real.pi)) < 0 := by
      apply Real.log_neg (by positivity)
      rw [div_lt_one (by linarith)]
      linarith
    simp [Operator.logPos, max_eq_right hlt.le]
  have hv4scale : v4LogScale 1 ![Real.pi, Real.pi] = 1 := by
    unfold v4LogScale
    rw [hmax, Real.sqrt_one, one_div, ← one_div, hlogzero 1 one_pos le_rfl]
    ring
  have hv4 : v4Majorant 1 ![Real.pi, Real.pi] = 1 / (1 + Real.pi ^ 2) := by
    unfold v4Majorant
    rw [hmax, hv4scale, Real.one_rpow, mul_one]
  have htheta : Operator.theta ![Real.pi, Real.pi] = 4 := by
    simp [Operator.theta, Operator.dispersion, Fin.sum_univ_two]
    norm_num
  have hdrift : Operator.driftlessMajorant 1 ![Real.pi, Real.pi] = 1 / 5 := by
    unfold Operator.driftlessMajorant
    rw [htheta]
    norm_num
  have hfscale : Operator.frequencyLogScale (1 / 4) 1 ![Real.pi, Real.pi] = 1 := by
    unfold Operator.frequencyLogScale
    rw [hmax, Real.sqrt_one, hlogzero (1 / 4) (by norm_num) (by norm_num)]
    ring
  have hcorr : Operator.correctedMajorant (1 / 4) 1 ![Real.pi, Real.pi]
      = 1 / Real.pi ^ 2 := by
    unfold Operator.correctedMajorant
    rw [if_neg (by rw [hmax]; exact hpi.ne'), hmax, hfscale, Real.one_rpow, mul_one]
  rw [Operator.frequencyMajorant, hv4, hdrift, hcorr]
  refine lt_min ?_ ?_
  · rw [div_lt_div_iff₀ (by nlinarith) (by norm_num)]
    nlinarith
  · rw [div_lt_div_iff₀ (by nlinarith) (by nlinarith)]
    nlinarith

/-- The scalar Move 1 hypothesis is satisfiable with `rl` equal to the value of the
minimization, so `move2_bound` is sharp. -/
theorem witness_move2_attained {h0 Z s C : ℝ} (hh0 : 0 < h0) (hZ : 0 < Z) (hC : 0 < C)
    (t : ℝ) :
    1 / (h0 + s ^ 2 * Z / C) ≤ (1 - s * (t * Z)) ^ 2 / h0 + C * (t ^ 2 * Z) := by
  have h := Manhattan.V4.oneVariable_le (s := s) hh0 hZ hC t
  have hEq : (1 - s * t * Z) ^ 2 / h0 + C * t ^ 2 * Z
      = (1 - s * (t * Z)) ^ 2 / h0 + C * (t ^ 2 * Z) := by ring
  linarith

/-- The Move 1 hypothesis of `resolvent_le_of_effectiveEnergy` is satisfiable with
`rl = 1/(h₀ + s² Z_δ/C)`, the conclusion's own right-hand side, which is strictly
positive. The proof runs through both substitution identities. -/
theorem witness_effectiveEnergy_attained {r0 delta h0 s C : ℝ}
    (hr0 : 0 < r0) (hr01 : r0 ≤ 1 / 4) (hdelta : 0 < delta) (hdle : delta ≤ r0 ^ 4)
    (hh0 : 0 < h0) (hC : 0 < C) (t : ℝ) :
    1 / (h0 + s ^ 2 * Zdelta r0 delta / C)
      ≤ (1 - s * gammaIntegral r0 delta (profile r0 delta t)) ^ 2 / h0
        + C * gammaIntegral r0 delta
            (fun r => effectiveWeight r * profile r0 delta t r ^ 2) := by
  have hsq : 0 < Real.sqrt delta := Real.sqrt_pos.2 hdelta
  have hsqle : Real.sqrt delta ≤ r0 := sqrt_le_of_le_pow_four hr0 hr01 hdle
  have hr0lt : r0 < 1 := lt_of_le_of_lt hr01 (by norm_num)
  rw [profile_gammaIntegral hsq hsqle t, energy_gammaIntegral hsq hsqle hr0lt t]
  exact witness_move2_attained hh0 (Zdelta_pos hr0 hr01 hdelta hdle) hC t

/-- The value bounded by `resolvent_le_of_effectiveEnergy` is strictly positive, so the
hypotheses do not force it to vanish. -/
theorem witness_effectiveEnergy_bound_pos {r0 delta h0 s C : ℝ}
    (hr0 : 0 < r0) (hr01 : r0 ≤ 1 / 4) (hdelta : 0 < delta) (hdle : delta ≤ r0 ^ 4)
    (hh0 : 0 < h0) (hC : 0 < C) :
    0 < 1 / (h0 + s ^ 2 * Zdelta r0 delta / C) := by
  have hZ : 0 < Zdelta r0 delta := Zdelta_pos hr0 hr01 hdelta hdle
  have hnn : 0 ≤ s ^ 2 * Zdelta r0 delta / C := by positivity
  exact div_pos one_pos (by linarith)

/-- The standing hypotheses of `move3_bound` are simultaneously satisfiable, with `s`
the intended `sin p₁`. Here `r₀ = 1/4`, `λ = 10⁻⁶`, `p = (1/2000, 0)`. -/
theorem witness_move3_hypotheses :
    Operator.maxFrequency ![(1 : ℝ) / 2000, 0] = 1 / 2000
      ∧ (2 / Real.pi) ^ 2 * Operator.maxFrequency ![(1 : ℝ) / 2000, 0] ^ 2
          ≤ Real.sin (1 / 2000) ^ 2
      ∧ Real.sqrt (1 / 10 ^ 6) + Operator.maxFrequency ![(1 : ℝ) / 2000, 0]
          ≤ ((1 : ℝ) / 4) ^ 4 := by
  have hmax : Operator.maxFrequency ![(1 : ℝ) / 2000, 0] = 1 / 2000 := by
    simp [Operator.maxFrequency]
  have hsqrt : Real.sqrt (1 / 10 ^ 6 : ℝ) = 1 / 1000 := by
    rw [show (1 / 10 ^ 6 : ℝ) = (1 / 1000) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 1000)]
  refine ⟨hmax, ?_, ?_⟩
  · rw [hmax]
    refine sq_sin_ge ?_
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2000)]
    nlinarith [Real.two_le_pi]
  · rw [hmax, hsqrt]
    norm_num

end Manhattan.V4.Frequency
