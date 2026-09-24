import Mathlib
import Manhattan.MainTheorems
import Audit.Support.Vocabulary
import Audit.Support.Bridge

/-!
# Solution: Transience

The challenge module `Audit/Transience/Challenge.lean` imports only Mathlib and
states the theorem with one intentional `sorry`.  This solution imports the
repository together with `Audit.Support.Vocabulary`, a verbatim copy of the
challenge's vocabulary, and proves the byte-identical statement from
`Manhattan.transience` through the bridges in `Audit/Support/Bridge.lean`.
-/

namespace ManhattanAudit

open MeasureTheory
open scoped ENNReal

/-- **Theorem 1.1** (`thm:main`, `manuscript.tex:192-198`): for almost every
environment, the quenched Green series is finite at every site. -/
theorem transience :
    ∀ᵐ omega ∂environmentLaw,
      ∀ x : Site, discreteGreen omega x < ∞ := by
  exact Bridge.transience

end ManhattanAudit
