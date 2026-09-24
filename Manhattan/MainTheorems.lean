import Manhattan.Frozen.Main.Theorem11
import Manhattan.Frozen.Main.Theorem12
import Manhattan.Glue.Assembly

/-!
# Main results

The main theorems of the formalization of *The randomly oriented Manhattan
lattice in 2D is transient* (Bou-Rabee and Peres), stated here in full:
Theorem 1.1 (`thm:main`) and Theorem 1.2 (`thm:annealed`).

Each theorem below restates its certified counterpart in `Manhattan/Frozen/Main/`
and is proved by direct application of it.  The statement of
`Manhattan.transience` is byte-faithful to `Manhattan.Frozen.Main.theorem_1_1`.
The certified statement `Manhattan.Frozen.Main.theorem_1_2` is the proposition
`Manhattan.AnnealedGreenBound`; `Manhattan.annealed_green_bound` displays the
body of that definition, with its names fully qualified, so that the statement
can be read here.  Neither theorem has a hypothesis, and nothing is assumed
(see `ASSUMPTIONS.md`).

* `Manhattan.transience`: Theorem 1.1.  For almost every environment of the
  randomly oriented Manhattan lattice, the quenched Green series
  `∑_{n ≥ 0} p^ω_n(x, x)` is finite at every site `x`, so the walk is transient.
* `Manhattan.annealed_green_bound`: Theorem 1.2.  There is `C < ∞` with
  `∫_0^∞ e^{-λt} p̄_t(0,0) dt ≤ C` for every `λ ∈ (0,1]`, and
  `∫_0^∞ p̄_t(0,0) dt < ∞`, where `p̄_t(0,0)` is the annealed return probability
  of the continuous-time walk with total jump rate two.

Both reduce to the standard axioms (`propext`, `Classical.choice`,
`Quot.sound`); see `Manhattan/Meta/AxiomsAudit.lean`.
-/

open MeasureTheory Set
open scoped ENNReal

/-- **Theorem 1.1** (`thm:main`, `manuscript.tex:192-198`).  The certified
statement is `Manhattan.Frozen.Main.theorem_1_1`. -/
theorem Manhattan.transience :
    ∀ᵐ omega ∂Manhattan.environmentLaw,
      ∀ x : Manhattan.Site, Manhattan.discreteGreen omega x < ∞ := by
  exact Manhattan.Frozen.Main.theorem_1_1

/-- **Theorem 1.2** (`thm:annealed`, `manuscript.tex:207-214`).  The certified
statement is `Manhattan.Frozen.Main.theorem_1_2`, whose type
`Manhattan.AnnealedGreenBound` unfolds to the statement displayed here. -/
theorem Manhattan.annealed_green_bound :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      (∀ lambda : ℝ, 0 < lambda → lambda ≤ 1 →
        ∫⁻ t in Ici 0,
          ENNReal.ofReal (Real.exp (-lambda * t)) *
            Manhattan.annealedContinuousKernel t 0 0 ≤ C) ∧
      ∫⁻ t in Ici 0, Manhattan.annealedContinuousKernel t 0 0 < ∞ := by
  exact Manhattan.Frozen.Main.theorem_1_2
