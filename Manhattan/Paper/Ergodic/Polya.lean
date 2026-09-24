/-
Pólya's theorem in two dimensions, and the unconditional counterexample.

`Recurrence.lean` carries `SimpleRandomWalkRecurrent` as the one named input it
does not prove.  It is discharged here by Pólya's theorem,
`LatticeProb.simpleRandomWalkRecurrent` of the library module
`LatticeProb.Walk.PolyaRecurrence`, so the counterexample of the closing remark
of the paper's open-questions section rests on nothing but the standard axioms.
-/
import LatticeProb.Walk.PolyaRecurrence
import Manhattan.Paper.Ergodic.Counterexample

namespace Manhattan.Paper.Ergodic

open MeasureTheory ProbabilityTheory
open scoped ENNReal symmDiff

/-- The alternating environment is recurrent, unconditionally. -/
theorem discreteGreen_altBase_eq_top' : discreteGreen altBase 0 = ⊤ :=
  discreteGreen_altBase_eq_top LatticeProb.simpleRandomWalkRecurrent

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
  stationary_ergodic_fair_not_transient LatticeProb.simpleRandomWalkRecurrent

end Manhattan.Paper.Ergodic

-- The three standard axioms only.
#print axioms LatticeProb.simpleRandomWalkRecurrent
#print axioms Manhattan.Paper.Ergodic.stationary_ergodic_fair_not_transient'
