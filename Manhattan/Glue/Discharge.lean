import Manhattan.Glue.DischargeSectors
import Manhattan.Glue.PropositionFrequency

/-!
# Discharge of the corrected energy interfaces

`Manhattan/Glue/DischargeSectors.lean` proves, unconditionally, that the
unnormalized objective of (24) is at most twice the paper's four-sector form
`E_p(f,k)` of (22). Combining that with Lemma 4.1 v3 and the normalization
identity (25), the whole remaining content of Proposition 2.2 is the single
paper estimate (23),
`E_p(f_p,k_p) ≤ C √L`,
for the explicit competitor `(f_p,k_p)` built in `Glue/Correction.lean`.

This file states (23) as the one named cross-module hypothesis
`ConcreteSectorEnergyBound` and discharges every downstream interface from
it: `CorrectedUnnormalizedEnergyInterface`,
`CorrectedHorizontalEnergyInterface`, the horizontal high-logarithmic
conclusion, `PropositionFrequencyClaim`, and the two headline providers.

Paper: `manuscript.tex:762-790` and `manuscript.tex:1134-1165`.
-/

noncomputable section

namespace Manhattan.Glue

open Manhattan.Estimates MeasureTheory
open scoped ENNReal

/-- The degree-one half of the concrete competitor `f_p`. -/
def correctedRowVector (d : LowDegreeCompetitorData) : WalshL2 :=
  Manhattan.degreeOneFrequencySynthesis Manhattan.Axis.horizontal d.rowFrequency

/-- The degree-three half of the concrete competitor `k_p`. -/
def correctedMixedVector (d : LowDegreeCompetitorData) : WalshL2 :=
  Manhattan.type112WalshSynthesis d.mixedCoefficient

theorem correctedRowVector_eq (d : LowDegreeCompetitorData) :
    correctedRowVector d =
      Manhattan.degreeOneFrequencySynthesis Manhattan.Axis.horizontal
        d.rowFrequency := rfl

theorem correctedMixedVector_eq (d : LowDegreeCompetitorData) :
    correctedMixedVector d =
      Manhattan.type112WalshSynthesis d.mixedCoefficient := rfl

theorem correctedRowVector_mem (d : LowDegreeCompetitorData) :
    correctedRowVector d ∈ Manhattan.walshDegree 1 :=
  d.row_mem_degree

theorem correctedMixedVector_mem (d : LowDegreeCompetitorData) :
    correctedMixedVector d ∈ Manhattan.walshDegree 3 :=
  d.mixed_mem_degree

/-- The exact cancellation (24) of the *normalized* competitor is the
vanishing of the degree-zero component of the unnormalized residual. -/
theorem inner_empty_unnormalizedResidual_eq_zero (d : LowDegreeCompetitorData)
    (p : Fin 2 → ℝ) (hcancel : d.CancelsAt p) :
    inner ℂ (Manhattan.walshL2 ∅)
      (unnormalizedResidual p d.normalization (correctedRowVector d)
        (correctedMixedVector d)) = 0 := by
  have hb : ((d.normalization : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr d.normalization_ne
  rw [LowDegreeCompetitorData.CancelsAt, LowDegreeCompetitorData.competitor,
    ← correctedRowVector_eq, ← correctedMixedVector_eq,
    map_smul, inner_sub_right, inner_smul_right, Manhattan.inner_walshL2,
    if_pos rfl] at hcancel
  rw [unnormalizedResidual, inner_sub_right, inner_smul_right,
    Manhattan.inner_walshL2, if_pos rfl]
  have hkey : ((d.normalization : ℝ) : ℂ)⁻¹ *
      inner ℂ (Manhattan.walshL2 ∅)
        (Manhattan.concreteFiberA p
          (correctedRowVector d + correctedMixedVector d)) = 1 := by
    linear_combination -hcancel
  field_simp at hkey
  rw [← hkey]
  ring

/-- `-- CROSS-LANE`: the paper's estimate (23), `E_p(f_p,k_p) ≤ C √L`, for
the concrete competitor of `Glue/Correction.lean`. The four summands of
`sectorObjective` are exactly the four summands of (22):
`⟨f,H₁f⟩`, `⟨k,H₃k⟩`, `‖D₁f-D₂^*k‖²_{-1}` and `‖D₃k‖²_{-1}`.

This is the sole remaining hypothesis of the whole formalization. It is
supplied by the concrete raising/lowering/multiplier/projection/cubic modules
together with the already-proved scalar bounds
`Manhattan.Estimates.lemmaFourTwoSuccessorV3Claim_proved` and
`Manhattan.Estimates.PropositionFiveTwoIntegralBound`. -/
def ConcreteSectorEnergyBound (M : ℝ) : Prop :=
  ∀ {lambda : ℝ}, ∀ hlambda : 0 < lambda,
    lambda ≤ 1 →
    ∀ p : Fin 2 → ℝ,
      p 0 ∈ Manhattan.Estimates.torus →
      p 1 ∈ Manhattan.Estimates.torus →
      |p 1| ≤ |p 0| →
      0 < |p 0| →
      let q : Manhattan.Estimates.Parameters :=
        ⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩
      q.logThreshold < q.scaleLog |p 0| →
      ∀ (hcert : Manhattan.Estimates.LemmaFourTwoIntegralCertificate q
          (p 0) (p 1))
        (hnormalization : Manhattan.Estimates.degreeOneNormalization q
          (p 0) ≠ 0),
        let d := correctedLowDegreeData hlambda p hcert hnormalization
        sectorObjective hlambda p d.normalization (correctedRowVector d)
            (correctedMixedVector d) ≤
          M * Real.sqrt (q.scaleLog |p 0|)

/-- The logarithmic scale is at least one. -/
theorem one_le_scaleLog (q : Manhattan.Estimates.Parameters) (a : ℝ) :
    1 ≤ q.scaleLog a := by
  rw [Manhattan.Estimates.Parameters.scaleLog]
  have hpos : (0 : ℝ) ≤ Manhattan.Estimates.logPos (q.r0 / q.delta a) :=
    le_max_left _ _
  linarith

/-- The four summands of (22), bounded separately, give (23). Each row of
the table supplies one conjunct. -/
theorem concreteSectorEnergyBound_of_summands {C₁ C₂ C₃ C₄ : ℝ}
    (hC₁ : 0 ≤ C₁)
    (h : ∀ {lambda : ℝ}, ∀ hlambda : 0 < lambda,
      lambda ≤ 1 →
      ∀ p : Fin 2 → ℝ,
        p 0 ∈ Manhattan.Estimates.torus →
        p 1 ∈ Manhattan.Estimates.torus →
        |p 1| ≤ |p 0| →
        0 < |p 0| →
        let q : Manhattan.Estimates.Parameters :=
          ⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩
        q.logThreshold < q.scaleLog |p 0| →
        ∀ (hcert : Manhattan.Estimates.LemmaFourTwoIntegralCertificate q
            (p 0) (p 1))
          (hnormalization : Manhattan.Estimates.degreeOneNormalization q
            (p 0) ≠ 0),
          let d := correctedLowDegreeData hlambda p hcert hnormalization
          (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hEnergy
              lambda (correctedRowVector d) ≤ C₁ ∧
            (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hEnergy
              lambda (correctedMixedVector d) ≤
                C₂ * Real.sqrt (q.scaleLog |p 0|) ∧
            (Manhattan.concreteFiberEnvironment.dissipativeSkewPair
                p).hMinusEnergy hlambda
              (walshSectorComponent (fun S => S.card = 2)
                (unnormalizedResidual p d.normalization (correctedRowVector d)
                  (correctedMixedVector d))) ≤
                C₃ * Real.sqrt (q.scaleLog |p 0|) ∧
            (Manhattan.concreteFiberEnvironment.dissipativeSkewPair
                p).hMinusEnergy hlambda
              (walshSectorComponent (fun S => S.card = 4)
                (unnormalizedResidual p d.normalization (correctedRowVector d)
                  (correctedMixedVector d))) ≤
                C₄ * Real.sqrt (q.scaleLog |p 0|)) :
    ConcreteSectorEnergyBound (C₁ + C₂ + C₃ + C₄) := by
  intro lambda hlambda hlambdaOne p hp₀ hp₁ horder hpositive
  let q : Manhattan.Estimates.Parameters :=
    ⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩
  change q.logThreshold < q.scaleLog |p 0| → _
  intro hlog hcert hnormalization d
  obtain ⟨h1, h2, h3, h4⟩ :=
    h hlambda hlambdaOne p hp₀ hp₁ horder hpositive hlog hcert hnormalization
  have hsqrt : 1 ≤ Real.sqrt (q.scaleLog |p 0|) :=
    Real.one_le_sqrt.mpr (one_le_scaleLog q |p 0|)
  have hC₁scale : C₁ ≤ C₁ * Real.sqrt (q.scaleLog |p 0|) :=
    le_mul_of_one_le_right hC₁ hsqrt
  show sectorObjective hlambda p d.normalization (correctedRowVector d)
      (correctedMixedVector d) ≤
    (C₁ + C₂ + C₃ + C₄) * Real.sqrt (q.scaleLog |p 0|)
  rw [sectorObjective]
  nlinarith [h1, h2, h3, h4, hC₁scale]

/-- Discharge of `Glue/EnergyAssembly.lean:54`: the model-specific remainder
after the exact cancellation (24)--(25) follows from (23) with the universal
factor two coming from the sector splitting. -/
theorem correctedUnnormalizedEnergyInterface_of_sectorEnergy {M : ℝ}
    (h : ConcreteSectorEnergyBound M) :
    CorrectedUnnormalizedEnergyInterface (2 * M) := by
  intro lambda hlambda hlambdaOne p hp₀ hp₁ horder hpositive
  let q : Manhattan.Estimates.Parameters :=
    ⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩
  change q.logThreshold < q.scaleLog |p 0| → _
  intro hlog hcert hnormalization d hcancels
  have hsector : sectorObjective hlambda p d.normalization
      (correctedRowVector d) (correctedMixedVector d) ≤
      M * Real.sqrt (q.scaleLog |p 0|) :=
    h hlambda hlambdaOne p hp₀ hp₁ horder hpositive hlog hcert hnormalization
  have hsplit := unnormalizedObjective_le_sectorObjective hlambda p
    d.normalization (correctedRowVector_mem d) (correctedMixedVector_mem d)
    (inner_empty_unnormalizedResidual_eq_zero d p hcancels)
  have hgoal :
      (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hEnergy
            lambda (correctedRowVector d + correctedMixedVector d) +
          (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy
            hlambda (unnormalizedResidual p d.normalization
              (correctedRowVector d) (correctedMixedVector d)) ≤
        2 * M * Real.sqrt (q.scaleLog |p 0|) := by
    calc
      _ ≤ 2 * sectorObjective hlambda p d.normalization
            (correctedRowVector d) (correctedMixedVector d) := hsplit
      _ ≤ 2 * (M * Real.sqrt (q.scaleLog |p 0|)) := by
        exact mul_le_mul_of_nonneg_left hsector (by norm_num)
      _ = 2 * M * Real.sqrt (q.scaleLog |p 0|) := by ring
  exact hgoal

/-- `Glue/PropositionFrequency.lean:28` from the single cross-module bound. -/
theorem correctedUnnormalizedEnergySupply_of_sectorEnergy {M : ℝ}
    (hM : 0 ≤ M) (h : ConcreteSectorEnergyBound M) :
    CorrectedUnnormalizedEnergySupply :=
  ⟨2 * M, by linarith, correctedUnnormalizedEnergyInterface_of_sectorEnergy h⟩

/-- `Glue/EnergyAssembly.lean:90` and `Glue/PropositionFrequency.lean:23`
from the single cross-module bound. -/
theorem correctedHorizontalEnergySupply_of_sectorEnergy {M : ℝ}
    (hM : 0 ≤ M) (h : ConcreteSectorEnergyBound M) :
    CorrectedHorizontalEnergySupply :=
  correctedHorizontalEnergySupply_of_unnormalized
    (correctedUnnormalizedEnergySupply_of_sectorEnergy hM h)

/-- The exact horizontal high-logarithmic conclusion of
`manuscript.tex:1137-1154`. -/
theorem correctedLowDegreeData_energy_horizontal_of_sectorEnergy {M : ℝ}
    (hM : 0 ≤ M) (h : ConcreteSectorEnergyBound M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {lambda : ℝ}, ∀ hlambda : 0 < lambda, lambda ≤ 1 →
        ∀ p : Fin 2 → ℝ,
          p 0 ∈ Manhattan.Estimates.torus →
          p 1 ∈ Manhattan.Estimates.torus →
          |p 1| ≤ |p 0| →
          0 < |p 0| →
          let q : Manhattan.Estimates.Parameters :=
            ⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩
          q.logThreshold < q.scaleLog |p 0| →
          ∃ (hcert : Manhattan.Estimates.LemmaFourTwoIntegralCertificate q
              (p 0) (p 1))
            (hnormalization : Manhattan.Estimates.degreeOneNormalization q
              (p 0) ≠ 0),
            let d := correctedLowDegreeData hlambda p hcert hnormalization
            (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hEnergy
                  lambda d.competitor +
                (Manhattan.concreteFiberEnvironment.dissipativeSkewPair
                    p).hMinusEnergy hlambda (Manhattan.walshL2 ∅ -
                  Manhattan.concreteFiberA p d.competitor) ≤
              C * Manhattan.Operator.correctedMajorant
                correctedCompetitorCutoff lambda p := by
  obtain ⟨C, hC, hinterface⟩ := correctedHorizontalEnergySupply_of_sectorEnergy hM h
  exact ⟨C, hC, fun hlambda => hinterface hlambda⟩

/-- Proposition 2.2 version 2 from the single cross-module bound. -/
theorem proposition_frequency_v2_of_sectorEnergy {M : ℝ} (hM : 0 ≤ M)
    (h : ConcreteSectorEnergyBound M) : PropositionFrequencyClaim :=
  proposition_frequency_v2_of_horizontalEnergy
    (correctedHorizontalEnergySupply_of_sectorEnergy hM h)

/-- Theorem 1.2 from the single cross-module bound. -/
theorem theorem_1_2_proved_of_sectorEnergy {M : ℝ} (hM : 0 ≤ M)
    (h : ConcreteSectorEnergyBound M) : Manhattan.AnnealedGreenBound :=
  theorem_1_2_of_proposition_frequency
    (proposition_frequency_v2_of_sectorEnergy hM h)

/-- Theorem 1.1 from the single cross-module bound. -/
theorem theorem_1_1_proved_of_sectorEnergy {M : ℝ} (hM : 0 ≤ M)
    (h : ConcreteSectorEnergyBound M) :
    ∀ᵐ omega ∂Manhattan.environmentLaw,
      ∀ x : Manhattan.Site, Manhattan.discreteGreen omega x < ∞ :=
  theorem_1_1_of_proposition_frequency
    (proposition_frequency_v2_of_sectorEnergy hM h)

end Manhattan.Glue
