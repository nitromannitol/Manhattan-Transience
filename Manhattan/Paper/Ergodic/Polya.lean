/-
Pólya's theorem in two dimensions, and the unconditional counterexample.

`Recurrence.lean` carried `SimpleRandomWalkRecurrent` as the one named input it
did not prove, because Mathlib has no recurrence theorem for random walks. It
is discharged here, so the counterexample of the closing remark of the paper's
open-questions section rests on nothing but the standard axioms.
-/
import Manhattan.Paper.Ergodic.Assemble
import Manhattan.Paper.Ergodic.OneD
import Manhattan.Paper.Ergodic.Harmonic
import Manhattan.Paper.Ergodic.Counterexample

namespace Manhattan.Paper.Ergodic

open MeasureTheory ProbabilityTheory
open scoped ENNReal symmDiff

/-- The planar return count. -/
theorem srwCount_two_mul (m : ℕ) : srwCount (2 * m) 0 = (Nat.centralBinom m) ^ 2 := by
  rw [srwCount_eq_sq, oneDCount_two_mul]

/-- **Pólya's theorem in two dimensions.** -/
theorem simpleRandomWalkRecurrent : SimpleRandomWalkRecurrent :=
  simpleRandomWalkRecurrent_of oneDCount_two_mul tsum_harmonic_eq_top

/-- The alternating environment is recurrent, unconditionally. -/
theorem discreteGreen_altBase_eq_top' : discreteGreen altBase 0 = ⊤ :=
  discreteGreen_altBase_eq_top simpleRandomWalkRecurrent

/-- **The closing remark of the open-questions section, unconditionally.**
Stationarity, ergodicity under the full translation group, and fair marginals
do not force transience. -/
theorem stationary_ergodic_fair_not_transient' :
    IsProbabilityMeasure ergodicLaw ∧
    (∀ x : Site, MeasurePreserving (translateEnvironment x) ergodicLaw ergodicLaw) ∧
    (∀ s : Set Environment,
      (∀ x : Site, ergodicLaw (s ∆ (translateEnvironment x ⁻¹' s)) = 0) →
        ergodicLaw s = 0 ∨ ergodicLaw s = 1) ∧
    (∀ (l : LineIndex) (o : Orientation),
      ergodicLaw {ω : Environment | ω l = o} = (2 : ℝ≥0∞)⁻¹) ∧
    (∀ᵐ ω ∂ergodicLaw, ∃ x : Site, ω = translateEnvironment x altBase) ∧
    (∀ᵐ ω ∂ergodicLaw, discreteGreen ω 0 = ⊤) :=
  stationary_ergodic_fair_not_transient simpleRandomWalkRecurrent

end Manhattan.Paper.Ergodic

-- The three standard axioms only.
#print axioms Manhattan.Paper.Ergodic.simpleRandomWalkRecurrent
#print axioms Manhattan.Paper.Ergodic.srwCount_two_mul
#print axioms Manhattan.Paper.Ergodic.stationary_ergodic_fair_not_transient'
