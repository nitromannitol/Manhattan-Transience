import Manhattan.Estimates.PropositionFiveTwoSupport
import Manhattan.Operator.Frequency

/-!
# Handoff to the abstract operator estimates

This module contains the sorry-free scalar glue between the explicit
frequency vocabulary and the abstract interfaces in `Manhattan.Operator`.
The concrete Walsh competitor and the concrete Green function remain model
data; the two interface theorems below state exactly what those modules must
supply.

Paper: `manuscript.tex:640-681`.
-/

noncomputable section

open scoped BigOperators

namespace Manhattan.Estimates

/-- The two estimate modules use the same one-dimensional dispersion. -/
theorem operator_dispersion_eq (s : ℝ) :
    Operator.dispersion s = dispersion s := rfl

/-- The operator successor and the estimates module use the same torus
fundamental domain. -/
theorem operator_frequencyTorus_eq_torus : Operator.frequencyTorus = torus := rfl

/-- The sum-based operator definition of `theta` agrees with the explicit
two-coordinate definition used in Sections 4--5. -/
theorem operator_theta_eq (p : Fin 2 → ℝ) :
    Operator.theta p = theta p := by
  simp [Operator.theta, Operator.dispersion, theta, dispersion, Fin.sum_univ_two]
  ring

/-- After identifying the cutoff and square radius, the logarithmic scales
in Proposition 2.2 and the explicit construction agree. -/
theorem operator_frequencyLogScale_eq_scaleLog (q : Parameters)
    (p : Fin 2 → ℝ) :
    Operator.frequencyLogScale q.r0 q.lambda p =
      q.scaleLog (Operator.maxFrequency p) := by
  simp [Operator.frequencyLogScale, Operator.logPos, Parameters.scaleLog,
    Parameters.delta, logPos, max_comm]

/-- `-- INTERFACE`: separate driftless and corrected competitors imply the
minimum bound expected by the operator layer. The witnesses may differ; the
proof selects the appropriate one pointwise in frequency. -/
theorem competitorBoundClaim_of_two_branches {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (D : Operator.FiberEnvironment E) (V : E) (r0 C : ℝ)
    (hr0 : 0 < r0) (hr0One : r0 < 1) (hC : 0 ≤ C)
    (hdriftless : ∀ (lambda : ℝ), ∀ hlambda : 0 < lambda,
      lambda ≤ 1 → ∀ p : Fin 2 → ℝ,
        ∃ g : E,
          (D.dissipativeSkewPair p).hEnergy lambda g +
              (D.dissipativeSkewPair p).hMinusEnergy
                hlambda (V - D.fiberA p g) ≤
            C * Operator.driftlessMajorant lambda p)
    (hcorrected : ∀ (lambda : ℝ), ∀ hlambda : 0 < lambda,
      lambda ≤ 1 → ∀ p : Fin 2 → ℝ,
        ∃ g : E,
          (D.dissipativeSkewPair p).hEnergy lambda g +
              (D.dissipativeSkewPair p).hMinusEnergy
                hlambda (V - D.fiberA p g) ≤
            C * Operator.correctedMajorant r0 lambda p) :
    Operator.CompetitorBoundClaim D V := by
  refine ⟨r0, C, hr0, hr0One, hC, ?_⟩
  intro lambda hlambda hlambdaOne p
  by_cases hle : Operator.driftlessMajorant lambda p ≤
      Operator.correctedMajorant r0 lambda p
  · obtain ⟨g, hg⟩ := hdriftless lambda hlambda hlambdaOne p
    refine ⟨g, ?_⟩
    simpa [Operator.frequencyMajorant, min_eq_left hle] using hg
  · obtain ⟨g, hg⟩ := hcorrected lambda hlambda hlambdaOne p
    refine ⟨g, ?_⟩
    have hle' : Operator.correctedMajorant r0 lambda p ≤
        Operator.driftlessMajorant lambda p := le_of_not_ge hle
    simpa [Operator.frequencyMajorant, min_eq_right hle'] using hg

/-- Torus-restricted two-branch constructor for the successor. -/
theorem competitorBoundClaimV2_of_two_branches {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (D : Operator.FiberEnvironment E) (V : E) (r0 C : ℝ)
    (hr0 : 0 < r0) (hr0One : r0 < 1) (hC : 0 ≤ C)
    (hdriftless : ∀ (lambda : ℝ), ∀ hlambda : 0 < lambda,
      lambda ≤ 1 → ∀ p : Fin 2 → ℝ,
        p 0 ∈ torus → p 1 ∈ torus →
        ∃ g : E,
          (D.dissipativeSkewPair p).hEnergy lambda g +
              (D.dissipativeSkewPair p).hMinusEnergy
                hlambda (V - D.fiberA p g) ≤
            C * Operator.driftlessMajorant lambda p)
    (hcorrected : ∀ (lambda : ℝ), ∀ hlambda : 0 < lambda,
      lambda ≤ 1 → ∀ p : Fin 2 → ℝ,
        p 0 ∈ torus → p 1 ∈ torus →
        ∃ g : E,
          (D.dissipativeSkewPair p).hEnergy lambda g +
              (D.dissipativeSkewPair p).hMinusEnergy
                hlambda (V - D.fiberA p g) ≤
            C * Operator.correctedMajorant r0 lambda p) :
    Operator.CompetitorBoundClaimV2 D V := by
  refine ⟨r0, C, hr0, hr0One, hC, ?_⟩
  intro lambda hlambda hlambdaOne p hp0 hp1
  rw [operator_frequencyTorus_eq_torus] at hp0 hp1
  by_cases hle : Operator.driftlessMajorant lambda p ≤
      Operator.correctedMajorant r0 lambda p
  · obtain ⟨g, hg⟩ := hdriftless lambda hlambda hlambdaOne p hp0 hp1
    refine ⟨g, ?_⟩
    simpa [Operator.frequencyMajorant, min_eq_left hle] using hg
  · obtain ⟨g, hg⟩ := hcorrected lambda hlambda hlambdaOne p hp0 hp1
    refine ⟨g, ?_⟩
    have hle' : Operator.correctedMajorant r0 lambda p ≤
        Operator.driftlessMajorant lambda p := le_of_not_ge hle
    simpa [Operator.frequencyMajorant, min_eq_right hle'] using hg

end Manhattan.Estimates
