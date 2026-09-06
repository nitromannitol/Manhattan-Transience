import Manhattan.Estimates.DegreeOne
import Manhattan.Estimates.DegreeThree
import Manhattan.Estimates.FinsetRaising

/-!
# Frozen-candidate statement surface for Sections 4--5

These proposition-valued definitions record the exact remaining analytic
obligations without introducing axioms or unregistered placeholders. They are
intended to become frozen theorem blocks when the wave-2 manifest owner
registers the corresponding `DRAFT_SORRY` nodes.
-/

open MeasureTheory Set

namespace Manhattan.Estimates

noncomputable section

/-- Equation (22), with normalized Haar measure on `(-π,π]`. -/
def LineResolventIdentity : Prop :=
  ∀ mu : ℝ, 0 < mu →
    torusIntegral (fun r : ℝ => (mu + dispersion r)⁻¹) =
      (Real.sqrt (mu * (mu + 2)))⁻¹

/-- Lemma 4.1(a)--(d), with both `H⁻¹` norms expanded as weighted integrals. -/
def LemmaFourTwoClaim (K rho : ℝ) : Prop :=
  20 ≤ K → 0 < rho → rho ≤ Real.pi / 20 →
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ lambda : ℝ, 0 < lambda → lambda ≤ 1 →
    ∀ p₁ p₂ : ℝ, p₁ ∈ torus → p₂ ∈ torus → |p₂| ≤ |p₁| →
      let q : Parameters := ⟨lambda, K, rho⟩
      q.logThreshold < q.scaleLog |p₁| →
      degreeZeroAdjoint p₁ (degreeOneCoefficient q p₁) =
          -(degreeOneNormalization q p₁ : ℂ) ∧
      c * |p₁| * q.scaleLog |p₁| ≤ degreeOneNormalization q p₁ ∧
      degreeOneEnergy q p₁ ≤ C ∧
      (∀ r : ℝ, mixedResidual q p₁ r = signedSupportIndicator q p₁ r) ∧
      c * q.scaleLog |p₁| ≤ mixedResidualHMinusSq q p₁ ∧
      mixedResidualHMinusSq q p₁ ≤ C * q.scaleLog |p₁| ∧
      twoRowResidualHMinusSq q p₁ p₂ (degreeOneCoefficient q p₁) ≤ C

/-- Admissibility for the functional minimization in (26). -/
def RankOneAdmissible (M : ℝ → ℝ) (J : Set ℝ) (u : ℝ → ℂ) : Prop :=
  IntegrableOn u (J ∩ torus) ∧
  IntegrableOn (fun alpha : ℝ => M alpha * ‖u alpha‖ ^ 2) (J ∩ torus)

/-- Equations (26)--(27), stated by attainment and a universal lower bound;
this avoids the junk value of real `sInf` on an unbounded-below set. -/
def RankOneMinimizationClaim : Prop :=
  ∀ (B : ℝ) (M : ℝ → ℝ) (J : Set ℝ) (eta w : ℂ),
    0 < B → MeasurableSet J →
    (∀ alpha ∈ J ∩ torus, 0 < M alpha) →
    IntegrableOn (fun alpha : ℝ => (M alpha)⁻¹) (J ∩ torus) →
    RankOneAdmissible M J (rankOneMinimizer B M J eta w) ∧
    rankOneEnergy B M J eta w (rankOneMinimizer B M J eta w) =
      ‖w‖ ^ 2 / (B + rankOneSigma eta M J) ∧
    ∀ u : ℝ → ℂ, RankOneAdmissible M J u →
      ‖w‖ ^ 2 / (B + rankOneSigma eta M J) ≤ rankOneEnergy B M J eta w u

/-- Equation (29), with constants uniform in `λ,β,α` and depending only on
the fixed construction parameters. -/
def MultiplierComparisonClaim (K rho : ℝ) : Prop :=
  20 ≤ K → 0 < rho → rho ≤ Real.pi / 20 →
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ lambda : ℝ, 0 < lambda → lambda ≤ 1 →
    ∀ beta alpha : ℝ, |alpha| ≤ rho →
      4 * K * (Real.sqrt lambda + |beta|) ≤ |alpha| →
      let q : Parameters := ⟨lambda, K, rho⟩
      c * |alpha| ≤ multiplier 40 q (mixedTotalFrequency beta alpha) ∧
      multiplier 40 q (mixedTotalFrequency beta alpha) ≤ C * |alpha|

/-- Equation (29) follows with constants `80 / π` and `200`. -/
theorem multiplierComparisonClaim_proved (K rho : ℝ) :
    MultiplierComparisonClaim K rho := by
  intro hK _hrhoPos hrho
  refine ⟨80 / Real.pi, 200, div_pos (by norm_num) Real.pi_pos,
    by norm_num, ?_⟩
  intro lambda hlam hlamOne beta alpha halpha hseparation
  exact multiplier_comparison_explicit hK hrho hlam hlamOne halpha hseparation

/-- Proposition 4.2, Steps 1--3, after Lemma 5.4 supplies the coefficient
calculation. The three conjuncts are respectively (33), (34), and the final
`r` integral. -/
def PropositionFiveTwoClaim (K rho : ℝ) : Prop :=
  20 ≤ K → 0 < rho → rho ≤ Real.pi / 20 →
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ lambda : ℝ, 0 < lambda → lambda ≤ 1 →
    ∀ a : ℝ, 0 ≤ a →
      let q : Parameters := ⟨lambda, K, rho⟩
      K * q.delta a < q.r0 →
      DenominatorBound 40 c q a ∧ BetaIntegralBound 40 C q a ∧
        PropositionFiveTwoIntegralBound 40 C q a

/-- The direct the Finset convention formulation of the full Lemma 5.2 interface: the
operator-side energy is bounded by the explicit multiplier quadratic form.
The actual operators and coefficient carrier are supplied by the Walsh part.
-/
-- INTERFACE: the Walsh part supplies the concrete coefficient carrier and forms.
def LemmaSixTwoInterface {E : Type*}
    (hThree dFour multiplierForm : E → ℝ) : Prop :=
  ∀ k : E, hThree k + dFour k ≤ multiplierForm k

/-- The four claims established in Lemma 5.4. In the Finset convention, the fourth claim is
the direct reduction estimate: there is no projection-error term or Lemma 5.3. -/
-- INTERFACE: the Walsh part replaces these fields by concrete Finset identities.
structure LemmaSixFourCertificate where
  /-- The two supports are disjoint. -/
  supportDisjoint : Prop
  /-- The two-row component of the residual vanishes. -/
  twoRowComponentVanishes : Prop
  /-- The negative-frequency error is bounded. -/
  negativeFrequencyErrorBound : Prop
  /-- The direct reduction estimate, which in the Finset convention replaces the projection-error term. -/
  directReductionBound : Prop

end

end Manhattan.Estimates
