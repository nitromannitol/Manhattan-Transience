import Mathlib
import Audit.Support.Vocabulary

/-!
# The audited statements in the challenge environment

Each audited statement, elaborated as a proposition in exactly the environment
of the challenges: this module imports only Mathlib and the vocabulary.
`Audit/StatementRegression.lean` checks that each solution theorem has
exactly this type, so that no repository name or instance leaks into a
solution statement.
-/

namespace ManhattanAudit.Statements

open ManhattanAudit MeasureTheory Set
open scoped ENNReal

/-- The statement of `Audit/Transience/Challenge.lean`. -/
def transience : Prop :=
    ∀ᵐ omega ∂environmentLaw,
      ∀ x : Site, discreteGreen omega x < ∞

/-- The statement of `Audit/AnnealedGreenBound/Challenge.lean`. -/
def annealedGreenBound : Prop :=
    ∃ C : ℝ≥0∞, C < ∞ ∧
      (∀ lambda : ℝ, 0 < lambda → lambda ≤ 1 →
        ∫⁻ t in Ici 0,
          ENNReal.ofReal (Real.exp (-lambda * t)) * annealedContinuousKernel t 0 0 ≤ C) ∧
      ∫⁻ t in Ici 0, annealedContinuousKernel t 0 0 < ∞

end ManhattanAudit.Statements
