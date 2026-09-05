/-
# Certificate

The single file to read, and to run, if you want to know what this development
proves.  It restates the main results in self-contained form and prints the
axioms each one rests on.  Building this file checks everything it claims:

    lake build Manhattan.Certificate

Every `#print axioms` below must report exactly
`[propext, Classical.choice, Quot.sound]`, the three axioms of Lean's standard
classical foundation.  Anything else, in particular `sorryAx`, would mean a gap.

What is NOT certified is stated at the end, and in `VERIFICATION.md`.
-/
import Manhattan.Frozen
import Manhattan.MainTheorems
import Manhattan.V4.Move2Supply
import Manhattan.Paper.HeatKernel
import Manhattan.Paper.AnnealedDerivative
import Manhattan.Paper.Ergodic.Polya
import Manhattan.Operator.Variational

namespace Manhattan.Certificate

open MeasureTheory

/-! ## Theorem 1.1: the walk is transient in almost every environment

`discreteGreen ω x` is `∑' n, p_n^ω(x, x)`, the quenched Green function at `x`;
`environmentLaw` gives every lattice line an independent fair orientation. -/

theorem transience :
    ∀ᵐ ω ∂environmentLaw, ∀ x : Site, discreteGreen ω x < ⊤ :=
  Manhattan.Frozen.Main.theorem_1_1

/-- The same theorem by an independent second route, through the Version 4
competitor rather than the original construction. -/
theorem transience_second_route :
    ∀ᵐ ω ∂environmentLaw, ∀ x : Site, discreteGreen ω x < ⊤ :=
  Manhattan.V4.theorem_1_1_v4

/-! ## Theorem 1.2: the annealed Green function is finite -/

theorem annealed_green_finite : Manhattan.AnnealedGreenBound :=
  Manhattan.V4.annealedGreenBound_proved

/-! ## Proposition 6.1: the heat kernel and its time derivative -/

/-- `eq:heat-kernel`, uniformly in the environment and in both sites. -/
theorem heat_kernel_bound (ω : Environment) {t : ℝ} (ht : 0 ≤ t) (x y : Site) :
    Manhattan.Paper.ck ω t x y ≤ 2 / (t + 2) :=
  Manhattan.Paper.ck_le_two_div ω ht x y

/-- `eq:time-derivative`, for the annealed return probability the paper states
it for. -/
theorem annealed_derivative_bound {t : ℝ} (ht : 0 < t) :
    |deriv Manhattan.Paper.annealedReal t| ≤ 2 / (Real.sqrt t * (1 + t / 4)) :=
  Manhattan.Paper.abs_deriv_annealedReal_le ht

/-! ## The closing remark of the open questions

Stationarity, ergodicity under the full translation group and fair one-point
marginals do NOT force transience.  The witness is a random shift of the
alternating environment.  Pólya's theorem in two dimensions, which Mathlib does
not have, is proved here rather than assumed. -/

theorem ergodic_counterexample :
    ∀ᵐ ω ∂Manhattan.Paper.Ergodic.ergodicLaw,
      Manhattan.discreteGreen ω 0 = ⊤ :=
  (Manhattan.Paper.Ergodic.stationary_ergodic_fair_not_transient').2.2.2.2.2

theorem polya_two_dimensions : Manhattan.Paper.Ergodic.SimpleRandomWalkRecurrent :=
  Manhattan.Paper.Ergodic.simpleRandomWalkRecurrent

/-! ## Lemma 2.2: the variational bound, with no hypothesis on the competitor -/

theorem variational_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (P : Manhattan.Operator.DissipativeSkewPair E) {lambda : ℝ}
    (hlambda : 0 < lambda) (V g : E) :
    0 ≤ P.resolventQuadratic hlambda V ∧
      P.resolventQuadratic hlambda V ≤
        P.hEnergy lambda g + P.hMinusEnergy hlambda (V - P.A g) :=
  P.variational_bound hlambda V g

end Manhattan.Certificate

/-! ## The axiom audit

Each line must print exactly `[propext, Classical.choice, Quot.sound]`. -/

#print axioms Manhattan.Certificate.transience
#print axioms Manhattan.Certificate.transience_second_route
#print axioms Manhattan.Certificate.annealed_green_finite
#print axioms Manhattan.Certificate.heat_kernel_bound
#print axioms Manhattan.Certificate.annealed_derivative_bound
#print axioms Manhattan.Certificate.ergodic_counterexample
#print axioms Manhattan.Certificate.polya_two_dimensions
#print axioms Manhattan.Certificate.variational_bound
