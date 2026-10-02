import Mathlib

/-!
# Theorem 1.2 (`thm:annealed`): comparator challenge

Mathlib-only comparator challenge for Theorem 1.2 (`thm:annealed`,
`manuscript.tex:207-214`) of Bou-Rabee and Peres, *The randomly oriented
Manhattan lattice in 2D is transient*.  The certified statement is
`Manhattan.Frozen.Main.theorem_1_2`, restated in full in
`Manhattan/MainTheorems.lean` as `Manhattan.annealed_green_bound`.  Content:
there is `C < ∞` with `∫_0^∞ e^{-λt} p̄_t(0,0) dt ≤ C` for every `λ ∈ (0,1]`,
and `∫_0^∞ p̄_t(0,0) dt < ∞`, where `p̄_t(0,0)` is the annealed return
probability of the continuous-time walk with total jump rate two.

Only Mathlib is imported.  The vocabulary between `VOCABULARY-BEGIN` and
`VOCABULARY-END` rebuilds, from Mathlib primitives, every definition needed to
read the theorem: the sites and directed lines of `ℤ²`, the fair-coin
environment law, the quenched one-step and `n`-step kernels, the discrete Green
series, and the rate-two Poisson subordination that defines the continuous-time
kernel.  It is a statement-level copy of the repository definitions (see
`ManhattanAudit/README.md` for the provenance table) and is byte-identical in both
challenges.  The sole intentional `sorry` is the proof of the final theorem.

## Presentation deltas

None at the level of the displayed statement: the theorem below is the
statement of `Manhattan.annealed_green_bound`, which is the body of the
repository definition `Manhattan.AnnealedGreenBound` written out, with every
repository name replaced by its vocabulary copy.  The continuous-time kernel is
defined by Poisson subordination of the discrete kernel rather than as the
transition function of a continuous-time Markov process; `ManhattanAudit/DESIGN.md`
records this reading.
-/

-- VOCABULARY-BEGIN
namespace ManhattanAudit

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

/-! ## 1. Sites, directed lines and the fair-coin environment (`manuscript.tex:167-184`) -/

/-- The two coordinate directions of the Manhattan lattice. -/
inductive Axis
  | horizontal
  | vertical
  deriving DecidableEq, Fintype, Inhabited

instance : MeasurableSpace Axis := ⊤

instance : MeasurableSingletonClass Axis := ⟨fun _ => MeasurableSpace.measurableSet_top⟩

/-- A lattice site. -/
abbrev Site := ℤ × ℤ

/-- A directed line: its axis and its transverse integer coordinate. -/
abbrev LineIndex := Axis × ℤ

/-- The two possible orientations, identified with the signs `-1` and `1`. -/
inductive Orientation
  | negative
  | positive
  deriving DecidableEq, Fintype, Inhabited

instance : MeasurableSpace Orientation := ⊤

instance : MeasurableSingletonClass Orientation :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

/-- The integer sign represented by an orientation. -/
def Orientation.sign : Orientation → ℤ
  | .negative => -1
  | .positive => 1

/-- An environment gives one orientation to every horizontal or vertical line. -/
abbrev Environment := LineIndex → Orientation

/-- The coordinate transverse to lines parallel to `i`. -/
def transverseCoordinate (z : Site) : Axis → ℤ
  | .horizontal => z.2
  | .vertical => z.1

/-- The line of axis `i` through the site `z`. -/
def lineAt (z : Site) (i : Axis) : LineIndex := (i, transverseCoordinate z i)

/-- The positive coordinate vector parallel to `i`. -/
def basisStep : Axis → Site
  | .horizontal => (1, 0)
  | .vertical => (0, 1)

/-- The endpoint of the directed edge of type `i` leaving `z`. -/
def directedNeighbor (ω : Environment) (z : Site) (i : Axis) : Site :=
  z + ((ω (lineAt z i)).sign • basisStep i)

/-- The fair coin on the two orientations. -/
noncomputable def fairCoinPMF : PMF Orientation :=
  PMF.uniformOfFintype Orientation

/-- The fair-coin measure on one line orientation. -/
noncomputable def fairCoin : Measure Orientation := fairCoinPMF.toMeasure

instance : IsProbabilityMeasure fairCoin := by
  unfold fairCoin
  infer_instance

/-- The product fair-coin law `P` on environments. -/
noncomputable def environmentLaw : Measure Environment :=
  Measure.infinitePi (fun _ : LineIndex => fairCoin)

instance : IsProbabilityMeasure environmentLaw := by
  unfold environmentLaw
  infer_instance

/-! ## 2. Quenched discrete-time kernels (`manuscript.tex:176-198`) -/

/-- Follow a finite word of horizontal/vertical choices in a fixed environment. -/
def followPath (ω : Environment) (z : Site) : List Axis → Site
  | [] => z
  | i :: path => followPath ω (directedNeighbor ω z i) path

/-- Equation (1): the quenched one-step transition kernel. -/
noncomputable def oneStepKernel (ω : Environment) (z z' : Site) : ℝ≥0 :=
  (2 : ℝ≥0)⁻¹ * ∑ i : Axis, if z' = directedNeighbor ω z i then 1 else 0

/-- The quenched `n`-step transition kernel, as a finite path count. -/
noncomputable def nStepKernel (ω : Environment) (n : ℕ) (z z' : Site) : ℝ≥0 :=
  (2 : ℝ≥0)⁻¹ ^ n *
    ∑ path : Fin n → Axis,
      if followPath ω z (List.ofFn path) = z' then 1 else 0

/-- The quenched discrete Green series. -/
noncomputable def discreteGreen (ω : Environment) (x : Site) : ℝ≥0∞ :=
  ∑' n : ℕ, (nStepKernel ω n x x : ℝ≥0∞)

/-! ## 3. Rate-two Poisson subordination (`manuscript.tex:200-214`) -/

/-- The probability `P(N_t=n)` for a rate-two Poisson process.  It is set to
zero at negative times so that ordinary Lebesgue integration on `ℝ` can be
used without a separate subtype carrier. -/
noncomputable def rateTwoPoissonWeight (t : ℝ) (n : ℕ) : ℝ≥0∞ :=
  if ht : 0 ≤ t then
    poissonMeasure ⟨2 * t, mul_nonneg (by norm_num) ht⟩ {n}
  else 0

/-- The continuous-time quenched kernel, by rate-two Poisson subordination. -/
noncomputable def continuousKernel (ω : Environment) (t : ℝ) (z z' : Site) : ℝ≥0∞ :=
  ∑' n : ℕ, rateTwoPoissonWeight t n * nStepKernel ω n z z'

/-- The annealed continuous-time kernel. -/
noncomputable def annealedContinuousKernel (t : ℝ) (z z' : Site) : ℝ≥0∞ :=
  ∫⁻ ω, continuousKernel ω t z z' ∂environmentLaw

end ManhattanAudit
-- VOCABULARY-END

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
  sorry

end ManhattanAudit
