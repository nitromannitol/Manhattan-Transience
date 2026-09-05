import Manhattan.Glue.SummandsDegreeOne
import Manhattan.Glue.Discharge

/-!
# The four summands of (22), separately

`Manhattan.Glue.concreteSectorEnergyBound_of_summands` reduces the paper's estimate (23),
`E_p(f_p,k_p) ≤ C√L`, to four separate bounds, one for each summand of the
four-sector form (22) at `manuscript.tex:769-772`.  This file names those
four bounds, discharges the first of them unconditionally, and re-assembles
`ConcreteSectorEnergyBound` from the four.

The naming follows the table of :

| # | Term | Paper |
|---|---|---|
| 1 | `SummandOneBound` | `⟨f,H₁f⟩` |
| 2 | `SummandTwoBound` | `⟨k,H₃k⟩` |
| 3 | `SummandThreeBound` | `‖D₁f-D₂^*k‖²_{-1}` (the degree-two sector) |
| 4 | `SummandFourBound` | `‖D₃k‖²_{-1}` (the degree-four sector) |

Paper: `manuscript.tex:762-790`, `manuscript.tex:1134-1165`.
-/

noncomputable section

open MeasureTheory Set
open ComplexConjugate InnerProductSpace RCLike

namespace Manhattan.Glue

/-! ### The four summand statements -/

/-- Summand 1 of (22): `⟨f_p,H₁f_p⟩ ≤ C`. -/
def SummandOneBound (C : ℝ) : Prop :=
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
      ∀ (hcert : Manhattan.Estimates.LemmaFourTwoIntegralCertificate q (p 0) (p 1))
        (hnormalization : Manhattan.Estimates.degreeOneNormalization q (p 0) ≠ 0),
        let d := correctedLowDegreeData hlambda p hcert hnormalization
        (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hEnergy
          lambda (correctedRowVector d) ≤ C

/-- Summand 2 of (22): `⟨k_p,H₃k_p⟩ ≤ C√L`. -/
def SummandTwoBound (C : ℝ) : Prop :=
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
      ∀ (hcert : Manhattan.Estimates.LemmaFourTwoIntegralCertificate q (p 0) (p 1))
        (hnormalization : Manhattan.Estimates.degreeOneNormalization q (p 0) ≠ 0),
        let d := correctedLowDegreeData hlambda p hcert hnormalization
        (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hEnergy
            lambda (correctedMixedVector d) ≤
          C * Real.sqrt (q.scaleLog |p 0|)

/-- Summand 3 of (22): `‖D₁f_p-D₂^*k_p‖²_{-1} ≤ C√L`, i.e. the degree-two
Walsh sector of the unnormalized residual. -/
def SummandThreeBound (C : ℝ) : Prop :=
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
      ∀ (hcert : Manhattan.Estimates.LemmaFourTwoIntegralCertificate q (p 0) (p 1))
        (hnormalization : Manhattan.Estimates.degreeOneNormalization q (p 0) ≠ 0),
        let d := correctedLowDegreeData hlambda p hcert hnormalization
        (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy
            hlambda
            (walshSectorComponent (fun S => S.card = 2)
              (unnormalizedResidual p d.normalization (correctedRowVector d)
                (correctedMixedVector d))) ≤
          C * Real.sqrt (q.scaleLog |p 0|)

/-- Summand 4 of (22): `‖D₃k_p‖²_{-1} ≤ C√L`, i.e. the degree-four Walsh
sector of the unnormalized residual. -/
def SummandFourBound (C : ℝ) : Prop :=
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
      ∀ (hcert : Manhattan.Estimates.LemmaFourTwoIntegralCertificate q (p 0) (p 1))
        (hnormalization : Manhattan.Estimates.degreeOneNormalization q (p 0) ≠ 0),
        let d := correctedLowDegreeData hlambda p hcert hnormalization
        (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy
            hlambda
            (walshSectorComponent (fun S => S.card = 4)
              (unnormalizedResidual p d.normalization (correctedRowVector d)
                (correctedMixedVector d))) ≤
          C * Real.sqrt (q.scaleLog |p 0|)

/-- The four summands give (23). -/
theorem concreteSectorEnergyBound_of_four {C₁ C₂ C₃ C₄ : ℝ} (hC₁ : 0 ≤ C₁)
    (h1 : SummandOneBound C₁) (h2 : SummandTwoBound C₂)
    (h3 : SummandThreeBound C₃) (h4 : SummandFourBound C₄) :
    ConcreteSectorEnergyBound (C₁ + C₂ + C₃ + C₄) := by
  refine concreteSectorEnergyBound_of_summands hC₁ ?_
  intro lambda hlambda hlambdaOne p hp₀ hp₁ horder hpositive
  let q : Manhattan.Estimates.Parameters :=
    ⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩
  change q.logThreshold < q.scaleLog |p 0| → _
  intro hlog hcert hnormalization
  exact ⟨h1 hlambda hlambdaOne p hp₀ hp₁ horder hpositive hlog hcert hnormalization,
    h2 hlambda hlambdaOne p hp₀ hp₁ horder hpositive hlog hcert hnormalization,
    h3 hlambda hlambdaOne p hp₀ hp₁ horder hpositive hlog hcert hnormalization,
    h4 hlambda hlambdaOne p hp₀ hp₁ horder hpositive hlog hcert hnormalization⟩

/-! ### Summand 1, unconditionally -/

/-- **Summand 1 of (22).**  With the `(shift)` phase of
`Manhattan.Glue.rowTorusShift` in place, the concrete degree-one energy
`⟨f_p,H₁f_p⟩` of the competitor of `Glue/Correction.lean` is *exactly* the
scalar `degreeOneEnergy` that Lemma 4.1 v3(b) bounds.  Before the phase was
installed the two weights `λ+d(p₁)+d(p₂+s)` and `λ+d(p₁)+d(r)` were only
comparable, with the universal factor three of
`Manhattan.Glue.rowWeight_le`. -/
theorem hEnergy_correctedRowVector_eq {q : Manhattan.Estimates.Parameters}
    (hlambda : 0 < q.lambda) (p : Fin 2 → ℝ)
    (hcert : Manhattan.Estimates.LemmaFourTwoIntegralCertificate q (p 0) (p 1))
    (hnormalization : Manhattan.Estimates.degreeOneNormalization q (p 0) ≠ 0) :
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hEnergy q.lambda
        (correctedRowVector
          (correctedLowDegreeData hlambda p hcert hnormalization)) =
      Manhattan.Estimates.degreeOneEnergy q (p 0) := by
  rw [correctedRowVector,
    correctedLowDegreeData_row_eq hlambda p hcert hnormalization,
    hEnergy_degreeOneRowShift, Manhattan.Estimates.degreeOneEnergy]

/-- **Summand 1 is discharged.**  Lemma 4.1 v3(b) supplies the constant. -/
theorem summandOneBound_proved : ∃ C : ℝ, 0 ≤ C ∧ SummandOneBound C := by
  obtain ⟨c, C, hc, hC, hmain⟩ :=
    Manhattan.Estimates.lemmaFourTwoSuccessorV3Claim_proved
      correctedCompetitorK correctedCompetitorRho
      (by simp [correctedCompetitorK])
      (by simp only [correctedCompetitorRho]; positivity)
      (by simp [correctedCompetitorRho])
  refine ⟨C, by linarith, ?_⟩
  intro lambda hlambda hlambdaOne p hp₀ hp₁ horder hpositive
  let q : Manhattan.Estimates.Parameters :=
    ⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩
  change q.logThreshold < q.scaleLog |p 0| → _
  intro hlog hcert hnormalization
  have hscalar := hmain lambda hlambda hlambdaOne (p 0) (p 1) hp₀ hp₁ horder
    hpositive hlog
  have hbound : Manhattan.Estimates.degreeOneEnergy q (p 0) ≤ C := hscalar.2.2.2.1
  have hkey := hEnergy_correctedRowVector_eq (q := q) hlambda p hcert
    hnormalization
  exact hkey.trans_le hbound

end Manhattan.Glue
