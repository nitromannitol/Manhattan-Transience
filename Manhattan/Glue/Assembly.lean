import Manhattan.Glue.Annealed
import Manhattan.Glue.Fiberwise
import Manhattan.Glue.GreenDensity
import Manhattan.Glue.JointFiberization
import Manhattan.Model.MainTheorem
import Manhattan.Operator.Frequency

/-!
# Abstract assembly handoffs

These sorry-free implications are the part of the final assembly already
justified by the operator layer. Concrete providers must still connect the
annealed kernel to the fixed-frequency resolvent and construct the regional
bounds.

Paper: `manuscript.tex:640-697`.
-/

noncomputable section

namespace Manhattan.Glue

open Filter MeasureTheory
open Manhattan.Operator
open scoped ENNReal

/-- A model-specific competitor gives the paper's fixed-frequency resolvent
majorant through the one-sided variational inequality. -/
theorem frequency_bound_of_competitor {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (D : FiberEnvironment E) (V : E) (h : CompetitorBoundClaim D V) :
    ∃ r0 C : ℝ, 0 < r0 ∧ r0 < 1 ∧ 0 ≤ C ∧
      ∀ (lambda : ℝ), ∀ hlambda : 0 < lambda, lambda ≤ 1 → ∀ p : Fin 2 → ℝ,
        (D.dissipativeSkewPair p).resolventQuadratic hlambda V ≤
          C * frequencyMajorant r0 lambda p :=
  frequency_resolvent_le_of_competitor D V h

/-- The three regional integral estimates imply a uniform Green bound. -/
theorem uniform_green_bound {green : ℝ → ℝ} (B : RegionalIntegralBounds green) :
    ∀ lambda : ℝ, 0 < lambda → lambda ≤ 1 →
      green lambda ≤ B.smallBound + 2 * B.middleCoefficient + B.outerBound := by
  intro lambda hlambda hlambda1
  exact uniform_green_bound_of_regional_bounds B hlambda hlambda1

/-- Once the annealed Theorem 1.2 assertion is available, the model layer's
Tonelli, Poisson-subordination, and translation argument gives Theorem 1.1. -/
theorem theorem_1_1_of_annealed (h : Manhattan.AnnealedGreenBound) :
    ∀ᵐ omega ∂Manhattan.environmentLaw,
      ∀ x : Manhattan.Site, Manhattan.discreteGreen omega x < ∞ :=
  Manhattan.theorem_1_1 h

/-- Exact assembly of Theorem 1.2 from the version-2 Proposition 2.2
statement. The hypothesis is discharged by W6A's provider, without importing
the draft frozen anchor. -/
theorem theorem_1_2_of_proposition_frequency
    (h : PropositionFrequencyClaim) : Manhattan.AnnealedGreenBound := by
  obtain ⟨B⟩ := exists_concreteRegionalIntegralBounds h
  exact annealedGreenBound_of_regional_identity
    (fun lambda ↦ Manhattan.Estimates.normalizedFrequencyIntegral
      (concreteGreenDensity lambda)) B concreteGreenIdentity

/-- The complete headline conclusion, conditional only on the exact
Proposition 2.2 statement. -/
theorem theorem_1_1_of_proposition_frequency
    (h : PropositionFrequencyClaim) :
    ∀ᵐ omega ∂Manhattan.environmentLaw,
      ∀ x : Manhattan.Site, Manhattan.discreteGreen omega x < ∞ :=
  Manhattan.theorem_1_1 (theorem_1_2_of_proposition_frequency h)

end Manhattan.Glue
