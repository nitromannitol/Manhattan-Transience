module

public import Mathlib
public import Manhattan.MainTheorems
public import ManhattanAudit.AnnealedGreenBound.SolutionBasic
public import ManhattanAudit.Support.AnnealedGreenBoundBridge

@[expose] public section

/-!
# Solution: AnnealedGreenBound

The challenge module `ManhattanAudit/AnnealedGreenBound/Challenge.lean` imports only
Mathlib and states the theorem with one intentional `sorry`.  This solution
imports the repository together with `ManhattanAudit.AnnealedGreenBound.SolutionBasic`,
a verbatim copy of the challenge's vocabulary, and proves the byte-identical statement
from `Manhattan.annealed_green_bound` through the bridge in
`ManhattanAudit/Support/AnnealedGreenBoundBridge.lean`.
-/

namespace ManhattanAudit

open MeasureTheory Set
open scoped ENNReal

/-- **Theorem 1.2** (`thm:annealed`, `manuscript.tex:207-214`): the annealed
Laplace transforms of the return probability are bounded uniformly in
`λ ∈ (0, 1]`, and the annealed Green function at the origin is finite. -/
theorem annealed_green_bound :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      (∀ lambda : ℝ, 0 < lambda → lambda ≤ 1 →
        ∫⁻ t in Ici 0,
          ENNReal.ofReal (Real.exp (-lambda * t)) * annealedContinuousKernel t 0 0 ≤ C) ∧
      ∫⁻ t in Ici 0, annealedContinuousKernel t 0 0 < ∞ := by
  have h := Manhattan.annealed_green_bound
  simp only [Bridge.annealedContinuousKernel_eq] at h
  exact h

end ManhattanAudit
