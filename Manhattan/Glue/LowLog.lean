import Manhattan.Glue.AxisSwap
import Manhattan.Glue.Correction
import Manhattan.Estimates.Competitor

/-!
# The low-logarithmic and zero-frequency competitors

When the logarithmic scale is below the fixed threshold, the zero competitor
already gives the corrected-frequency bound. At zero frequency the corrected
majorant is defined to be the driftless one, matching the separate convention
in the manuscript.

Paper: `manuscript.tex:1158-1165`.
-/

noncomputable section

namespace Manhattan.Glue

/-- The absolute constant used by the elementary low-logarithmic comparison. -/
noncomputable def correctedLowLogConstant : ℝ :=
  Real.pi ^ 2 / 2 * (2 * Real.log correctedCompetitorK + 3) ^ (3 / 2 : ℝ)

theorem correctedLowLogConstant_one_le : 1 ≤ correctedLowLogConstant := by
  have hpi : 2 ≤ Real.pi := Real.two_le_pi
  have hlog : 0 ≤ Real.log correctedCompetitorK := by
    apply Real.log_nonneg
    simp [correctedCompetitorK]
  have hthreshold : 1 ≤ 2 * Real.log correctedCompetitorK + 3 := by
    nlinarith
  have hpow : 1 ≤
      (2 * Real.log correctedCompetitorK + 3) ^ (3 / 2 : ℝ) :=
    Real.one_le_rpow hthreshold (by norm_num)
  unfold correctedLowLogConstant
  nlinarith [sq_nonneg (Real.pi - 2)]

theorem correctedLowLogConstant_nonneg : 0 ≤ correctedLowLogConstant :=
  zero_le_one.trans correctedLowLogConstant_one_le

/-- On the torus, the square of the largest coordinate is controlled by the
dispersion, which is the elementary estimate used at `manuscript.tex:1159`. -/
theorem maxFrequency_sq_le_piSq_mul_theta (p : Fin 2 → ℝ)
    (hp₀ : p 0 ∈ Manhattan.Estimates.torus)
    (hp₁ : p 1 ∈ Manhattan.Estimates.torus) :
    Manhattan.Operator.maxFrequency p ^ 2 ≤
      Real.pi ^ 2 / 2 * Manhattan.Operator.theta p := by
  have hp₀abs : |p 0| ≤ Real.pi := abs_le.2 ⟨hp₀.1.le, hp₀.2⟩
  have hp₁abs : |p 1| ≤ Real.pi := abs_le.2 ⟨hp₁.1.le, hp₁.2⟩
  have hpiSq : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  have hd₀ := (Manhattan.Estimates.dispersion_quadratic_bounds hp₀abs).1
  have hd₁ := (Manhattan.Estimates.dispersion_quadratic_bounds hp₁abs).1
  have hd₀' : 2 * (p 0) ^ 2 ≤
      Real.pi ^ 2 * Manhattan.Estimates.dispersion (p 0) := by
    calc
      2 * (p 0) ^ 2 ≤ Manhattan.Estimates.dispersion (p 0) * Real.pi ^ 2 :=
        (div_le_iff₀ hpiSq).1 (by simpa only using hd₀)
      _ = Real.pi ^ 2 * Manhattan.Estimates.dispersion (p 0) := mul_comm _ _
  have hd₁' : 2 * (p 1) ^ 2 ≤
      Real.pi ^ 2 * Manhattan.Estimates.dispersion (p 1) := by
    calc
      2 * (p 1) ^ 2 ≤ Manhattan.Estimates.dispersion (p 1) * Real.pi ^ 2 :=
        (div_le_iff₀ hpiSq).1 (by simpa only using hd₁)
      _ = Real.pi ^ 2 * Manhattan.Estimates.dispersion (p 1) := mul_comm _ _
  rw [Manhattan.Estimates.operator_theta_eq]
  simp only [Manhattan.Operator.maxFrequency, Manhattan.Estimates.theta]
  rcases max_cases |p 0| |p 1| with ⟨hmax, _⟩ | ⟨hmax, _⟩
  · rw [hmax, sq_abs]
    nlinarith [Manhattan.Estimates.dispersion_nonneg (p 1)]
  · rw [hmax, sq_abs]
    nlinarith [Manhattan.Estimates.dispersion_nonneg (p 0)]

private theorem driftless_mul_maxFrequency_sq_le (lambda : ℝ)
    (hlambda : 0 < lambda) (p : Fin 2 → ℝ)
    (hp₀ : p 0 ∈ Manhattan.Estimates.torus)
    (hp₁ : p 1 ∈ Manhattan.Estimates.torus) :
    Manhattan.Operator.driftlessMajorant lambda p *
        Manhattan.Operator.maxFrequency p ^ 2 ≤ Real.pi ^ 2 / 2 := by
  have htheta := maxFrequency_sq_le_piSq_mul_theta p hp₀ hp₁
  have hthetaNonneg := Manhattan.operatorTheta_nonneg p
  have hden : 0 < lambda + Manhattan.Operator.theta p :=
    add_pos_of_pos_of_nonneg hlambda hthetaNonneg
  rw [Manhattan.Operator.driftlessMajorant, one_div]
  rw [inv_mul_le_iff₀ hden]
  nlinarith [sq_nonneg Real.pi]

theorem frequencyLogScale_one_le (r0 lambda : ℝ) (p : Fin 2 → ℝ) :
    1 ≤ Manhattan.Operator.frequencyLogScale r0 lambda p := by
  unfold Manhattan.Operator.frequencyLogScale Manhattan.Operator.logPos
  exact le_add_of_nonneg_right (le_max_right _ _)

/-- The zero competitor in the one-sided variational formula gives exactly
the driftless resolvent estimate. -/
theorem concrete_resolventQuadratic_le_driftless {lambda : ℝ}
    (hlambda : 0 < lambda) (p : Fin 2 → ℝ) :
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).resolventQuadratic
        hlambda (Manhattan.walshL2 ∅) ≤
      Manhattan.Operator.driftlessMajorant lambda p := by
  exact ((Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).resolventQuadratic_le
    hlambda (Manhattan.walshL2 ∅) 0).trans <| by
      rw [map_zero, sub_zero, Manhattan.concrete_hMinusEnergy_empty hlambda p]
      simp [Manhattan.Operator.DissipativeSkewPair.hEnergy,
        Manhattan.Operator.DissipativeSkewPair.H]

/-- Below the Lemma 4.1 threshold, the driftless majorant is bounded by a
fixed multiple of the corrected majorant. -/
theorem driftlessMajorant_le_corrected_of_lowLog
    {lambda : ℝ} (hlambda : 0 < lambda) (p : Fin 2 → ℝ)
    (hp₀ : p 0 ∈ Manhattan.Estimates.torus)
    (hp₁ : p 1 ∈ Manhattan.Estimates.torus)
    (hlog :
      (Manhattan.Estimates.Parameters.scaleLog
          ⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩
          (Manhattan.Operator.maxFrequency p)) ≤
        Manhattan.Estimates.Parameters.logThreshold
          ⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩) :
    Manhattan.Operator.driftlessMajorant lambda p ≤
      correctedLowLogConstant *
        Manhattan.Operator.correctedMajorant correctedCompetitorCutoff lambda p := by
  let a := Manhattan.Operator.maxFrequency p
  by_cases ha : a = 0
  · rw [Manhattan.Operator.correctedMajorant, if_pos ha]
    exact le_mul_of_one_le_left
      (driftlessMajorant_nonneg hlambda p) correctedLowLogConstant_one_le
  · let L := Manhattan.Operator.frequencyLogScale
      correctedCompetitorCutoff lambda p
    let Lstar := 2 * Real.log correctedCompetitorK + 3
    have hscale : L =
        Manhattan.Estimates.Parameters.scaleLog
          ⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩ a := by
      dsimp [L, a]
      simpa [Manhattan.Estimates.Parameters.r0, correctedCompetitorCutoff] using
        (Manhattan.Estimates.operator_frequencyLogScale_eq_scaleLog
          (⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩ :
            Manhattan.Estimates.Parameters) p)
    have hthreshold :
        Manhattan.Estimates.Parameters.logThreshold
          ⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩ = Lstar := by
      rfl
    have hLle : L ≤ Lstar := by
      rw [hscale, ← hthreshold]
      exact hlog
    have hLone : 1 ≤ L := by
      exact frequencyLogScale_one_le correctedCompetitorCutoff lambda p
    have hLnonneg : 0 ≤ L := zero_le_one.trans hLone
    have hLstarOne : 1 ≤ Lstar := by
      dsimp [Lstar]
      have hlogK : 0 ≤ Real.log correctedCompetitorK := by
        apply Real.log_nonneg
        simp [correctedCompetitorK]
      nlinarith
    have hpow : L ^ (3 / 2 : ℝ) ≤ Lstar ^ (3 / 2 : ℝ) :=
      Real.rpow_le_rpow hLnonneg hLle (by norm_num)
    have haSq : 0 < a ^ 2 := sq_pos_of_ne_zero ha
    have hLPow : 0 < L ^ (3 / 2 : ℝ) :=
      Real.rpow_pos_of_pos (zero_lt_one.trans_le hLone) _
    have hden : 0 < a ^ 2 * L ^ (3 / 2 : ℝ) := mul_pos haSq hLPow
    have hbase := driftless_mul_maxFrequency_sq_le lambda hlambda p hp₀ hp₁
    have hproduct :
        Manhattan.Operator.driftlessMajorant lambda p *
            (a ^ 2 * L ^ (3 / 2 : ℝ)) ≤ correctedLowLogConstant := by
      calc
        Manhattan.Operator.driftlessMajorant lambda p *
              (a ^ 2 * L ^ (3 / 2 : ℝ)) =
            (Manhattan.Operator.driftlessMajorant lambda p * a ^ 2) *
              L ^ (3 / 2 : ℝ) := by ring
        _ ≤ (Real.pi ^ 2 / 2) * L ^ (3 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right hbase (Real.rpow_nonneg hLnonneg _)
        _ ≤ (Real.pi ^ 2 / 2) * Lstar ^ (3 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
        _ = correctedLowLogConstant := by
          rfl
    rw [Manhattan.Operator.correctedMajorant, if_neg ha]
    have hquotient : Manhattan.Operator.driftlessMajorant lambda p ≤
        correctedLowLogConstant / (a ^ 2 * L ^ (3 / 2 : ℝ)) :=
      (le_div_iff₀ hden).2 hproduct
    simpa only [a, L, div_eq_mul_inv, one_div, one_mul] using hquotient

/-- At zero maximum frequency, the corrected convention is the driftless
majorant and no logarithmic hypothesis is needed. -/
theorem driftlessMajorant_le_corrected_of_maxFrequency_eq_zero
    {lambda : ℝ} (hlambda : 0 < lambda) (p : Fin 2 → ℝ)
    (hzero : Manhattan.Operator.maxFrequency p = 0) :
    Manhattan.Operator.driftlessMajorant lambda p ≤
      correctedLowLogConstant *
        Manhattan.Operator.correctedMajorant correctedCompetitorCutoff lambda p := by
  rw [Manhattan.Operator.correctedMajorant, if_pos hzero]
  exact le_mul_of_one_le_left
    (driftlessMajorant_nonneg hlambda p) correctedLowLogConstant_one_le

/-- Zero coefficient data, whose synthesized Walsh competitor is exactly zero. -/
noncomputable def zeroLowDegreeCompetitorData : LowDegreeCompetitorData where
  rowFrequency := 0
  mixedCoefficient := 0
  normalization := 1
  normalization_ne := one_ne_zero

@[simp] theorem zeroLowDegreeCompetitorData_competitor :
    zeroLowDegreeCompetitorData.competitor = 0 := by
  simp [zeroLowDegreeCompetitorData, LowDegreeCompetitorData.competitor,
    Manhattan.degreeOneFrequencySynthesis, Manhattan.axisDegreeOneSynthesis,
    Manhattan.type112WalshSynthesis]

/-- The low-logarithmic branch of the corrected competitor certificate. -/
theorem correctedLowDegreeData_energy_lowLog
    {lambda : ℝ} (hlambda : 0 < lambda) (p : Fin 2 → ℝ)
    (hp₀ : p 0 ∈ Manhattan.Estimates.torus)
    (hp₁ : p 1 ∈ Manhattan.Estimates.torus)
    (hlog :
      (Manhattan.Estimates.Parameters.scaleLog
          ⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩
          (Manhattan.Operator.maxFrequency p)) ≤
        Manhattan.Estimates.Parameters.logThreshold
          ⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩) :
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hEnergy
          lambda zeroLowDegreeCompetitorData.competitor +
        (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy
          hlambda (Manhattan.walshL2 ∅ -
            Manhattan.concreteFiberA p zeroLowDegreeCompetitorData.competitor) ≤
      correctedLowLogConstant *
        Manhattan.Operator.correctedMajorant correctedCompetitorCutoff lambda p := by
  rw [zeroLowDegreeCompetitorData_competitor, map_zero, sub_zero,
    Manhattan.concrete_hMinusEnergy_empty hlambda p]
  simp only [Manhattan.Operator.DissipativeSkewPair.hEnergy,
    Manhattan.Operator.DissipativeSkewPair.H, map_zero, inner_zero_left,
    map_zero, zero_add]
  exact driftlessMajorant_le_corrected_of_lowLog hlambda p hp₀ hp₁ hlog

end Manhattan.Glue
