module

public import Mathlib
public import Manhattan.MainTheorems
public import ManhattanAudit.Transience.SolutionBasic
public import ManhattanAudit.Support.TransienceBridge

@[expose] public section

/-!
# Solution: Transience

The challenge module `ManhattanAudit/Transience/Challenge.lean` imports only Mathlib and
states the theorem with one intentional `sorry`.  This solution imports the
repository together with `ManhattanAudit.Transience.SolutionBasic`, a verbatim copy of the
challenge's vocabulary, and proves the byte-identical statement from
`Manhattan.transience` through the bridge in
`ManhattanAudit/Support/TransienceBridge.lean`.
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
