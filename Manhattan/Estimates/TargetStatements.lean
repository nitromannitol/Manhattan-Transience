import Manhattan.Estimates.DegreeOne
import Manhattan.Estimates.DegreeThree
import Manhattan.Estimates.FinsetRaising

/-!
# Statements of the analytic estimates of Sections 4--5

These proposition-valued definitions state the analytic estimates of Sections 4--5
that the assembly consumes.
-/

open MeasureTheory Set

namespace Manhattan.Estimates

noncomputable section

/-- Equation (22), with normalized Haar measure on `(-π,π]`. -/
def LineResolventIdentity : Prop :=
  ∀ mu : ℝ, 0 < mu →
    torusIntegral (fun r : ℝ => (mu + dispersion r)⁻¹) =
      (Real.sqrt (mu * (mu + 2)))⁻¹

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

end

end Manhattan.Estimates
