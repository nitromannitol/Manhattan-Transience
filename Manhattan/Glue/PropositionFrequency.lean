import Manhattan.Glue.EnergyAssembly
import Manhattan.Glue.GreenDensity
import Manhattan.Glue.Assembly

/-!
# Proposition 2.2 and the handoffs to the main theorems

The axis-swap and low-log branches reduce the whole fixed-frequency estimate
to one horizontal high-logarithmic supply.  Once the sector files discharge
that named interface, this file produces the exact `PropositionFrequencyClaim`
consumed by the already-proved implications.

Paper: `manuscript.tex:644-681` and `manuscript.tex:1134-1169`.
-/

noncomputable section

namespace Manhattan.Glue

open Filter MeasureTheory
open scoped ENNReal

/-- Existence of one universal constant for the complete horizontal energy
estimate.  DISCHARGED in `Glue/Discharge.lean` by
`correctedHorizontalEnergySupply_of_sectorEnergy`. -/
def CorrectedHorizontalEnergySupply : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ CorrectedHorizontalEnergyInterface C

/-- Existence of a universal constant for the unnormalized operator-sector
estimate.  DISCHARGED in `Glue/Discharge.lean` by
`correctedUnnormalizedEnergySupply_of_sectorEnergy`. -/
def CorrectedUnnormalizedEnergySupply : Prop :=
  ∃ M : ℝ, 0 ≤ M ∧ CorrectedUnnormalizedEnergyInterface M

/-- The actual Lemma 4.1/cancellation/normalization assembly converts the
remaining operator-sector supply to the horizontal supply. -/
theorem correctedHorizontalEnergySupply_of_unnormalized
    (hsupply : CorrectedUnnormalizedEnergySupply) :
    CorrectedHorizontalEnergySupply := by
  obtain ⟨M, hM, hsector⟩ := hsupply
  exact correctedHorizontalEnergyInterface_exists_of_unnormalized
    M hM hsector

/-- The complete torus-restricted Proposition 2.2 provider, conditional only
on the named horizontal supply. -/
theorem proposition_frequency_v2_of_horizontalEnergy
    (hsupply : CorrectedHorizontalEnergySupply) : PropositionFrequencyClaim := by
  obtain ⟨C, hC, hhorizontal⟩ := hsupply
  let Cglobal := C + correctedLowLogConstant + 1
  have hCglobalOne : 1 ≤ Cglobal := by
    dsimp [Cglobal]
    nlinarith [correctedLowLogConstant_nonneg]
  have hcorrected :
      ∀ (lambda : ℝ), ∀ hlambda : 0 < lambda, lambda ≤ 1 →
        ∀ p : Fin 2 → ℝ,
          p 0 ∈ Manhattan.Estimates.torus →
          p 1 ∈ Manhattan.Estimates.torus →
          ∃ g : Manhattan.WalshL2,
            (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hEnergy
                  lambda g +
                (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy
                  hlambda (Manhattan.walshL2 ∅ -
                    Manhattan.concreteFiberA p g) ≤
              Cglobal * Manhattan.Operator.correctedMajorant
                correctedCompetitorCutoff lambda p := by
    simpa only [Cglobal] using
      correctedCompetitor_all_frequencies_of_horizontal C hC hhorizontal
  have hdriftless :
      ∀ (lambda : ℝ), ∀ hlambda : 0 < lambda, lambda ≤ 1 →
        ∀ p : Fin 2 → ℝ,
          p 0 ∈ Manhattan.Estimates.torus →
          p 1 ∈ Manhattan.Estimates.torus →
          ∃ g : Manhattan.WalshL2,
            (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hEnergy
                  lambda g +
                (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy
                  hlambda (Manhattan.walshL2 ∅ -
                    Manhattan.concreteFiberA p g) ≤
              Cglobal * Manhattan.Operator.driftlessMajorant lambda p := by
    intro lambda hlambda _ p _ _
    obtain ⟨g, hg⟩ := concrete_driftless_competitor lambda hlambda p
    refine ⟨g, hg.trans ?_⟩
    exact le_mul_of_one_le_left (driftlessMajorant_nonneg hlambda p) hCglobalOne
  have hoperator : Manhattan.Operator.CompetitorBoundClaimV2
      Manhattan.concreteFiberEnvironment (Manhattan.walshL2 ∅) :=
    Manhattan.Estimates.competitorBoundClaimV2_of_two_branches
      Manhattan.concreteFiberEnvironment (Manhattan.walshL2 ∅)
      correctedCompetitorCutoff Cglobal correctedCompetitorCutoff_pos
      correctedCompetitorCutoff_lt_one (zero_le_one.trans hCglobalOne)
      hdriftless hcorrected
  obtain ⟨r0, C', hr0, hr0One, hC', hbound⟩ := hoperator
  exact ⟨Manhattan.concreteFiberEnvironment, rfl, rfl,
    r0, C', hr0, hr0One, hC', hbound⟩

/-- Proposition 2.2 conditional only on the final unnormalized
operator-sector supply. -/
theorem proposition_frequency_v2_of_unnormalizedEnergy
    (hsupply : CorrectedUnnormalizedEnergySupply) :
    PropositionFrequencyClaim :=
  proposition_frequency_v2_of_horizontalEnergy
    (correctedHorizontalEnergySupply_of_unnormalized hsupply)

/-- The Theorem 1.2 provider elaborates immediately from the conditional
Proposition 2.2 assembly. -/
theorem theorem_1_2_proved_of_horizontalEnergy
    (hsupply : CorrectedHorizontalEnergySupply) : Manhattan.AnnealedGreenBound :=
  theorem_1_2_of_proposition_frequency
    (proposition_frequency_v2_of_horizontalEnergy hsupply)

/-- The Theorem 1.1 provider elaborates immediately from the conditional
Proposition 2.2 assembly. -/
theorem theorem_1_1_proved_of_horizontalEnergy
    (hsupply : CorrectedHorizontalEnergySupply) :
    ∀ᵐ omega ∂Manhattan.environmentLaw,
      ∀ x : Manhattan.Site, Manhattan.discreteGreen omega x < ∞ :=
  theorem_1_1_of_proposition_frequency
    (proposition_frequency_v2_of_horizontalEnergy hsupply)

/-- The Theorem 1.2 provider conditional only on the remaining unnormalized
operator-sector supply. -/
theorem theorem_1_2_proved_of_unnormalizedEnergy
    (hsupply : CorrectedUnnormalizedEnergySupply) :
    Manhattan.AnnealedGreenBound :=
  theorem_1_2_of_proposition_frequency
    (proposition_frequency_v2_of_unnormalizedEnergy hsupply)

/-- The Theorem 1.1 provider conditional only on the remaining unnormalized
operator-sector supply. -/
theorem theorem_1_1_proved_of_unnormalizedEnergy
    (hsupply : CorrectedUnnormalizedEnergySupply) :
    ∀ᵐ omega ∂Manhattan.environmentLaw,
      ∀ x : Manhattan.Site, Manhattan.discreteGreen omega x < ∞ :=
  theorem_1_1_of_proposition_frequency
    (proposition_frequency_v2_of_unnormalizedEnergy hsupply)

end Manhattan.Glue
