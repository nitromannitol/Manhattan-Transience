module

public import Mathlib

@[expose] public section

/-!
# Statement-level audit vocabulary for the `AnnealedGreenBound` comparator

Verbatim copy of the vocabulary block of
`ManhattanAudit/AnnealedGreenBound/Challenge.lean` (between `VOCABULARY-BEGIN` and
`VOCABULARY-END`), Mathlib-only; a mechanical copy, not hand-edited.  The two
blocks must stay byte-identical so that the comparator's constant-by-constant
closure check passes.
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
  deriving DecidableEq, Inhabited

/-- The constructor list emitted by Mathlib's finite-enumeration deriving handler. -/
protected abbrev Axis.enumList : List Axis := [Axis.horizontal, Axis.vertical]

protected theorem Axis.enumList_getElem?_ctorIdx_eq (x : Axis) :
    Axis.enumList[Axis.ctorIdx x]? = some x := by
  cases x <;> rfl

protected theorem Axis.enumList_nodup : Axis.enumList.Nodup := by
  apply List.Nodup.of_map Axis.ctorIdx
  have h : List.map Axis.ctorIdx Axis.enumList = List.range 2 := rfl
  exact h ▸ List.nodup_range

instance : Fintype Axis where
  elems := Finset.mk Axis.enumList Axis.enumList_nodup
  complete := by
    intro x
    cases x <;> decide

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
  deriving DecidableEq, Inhabited

/-- The constructor list emitted by Mathlib's finite-enumeration deriving handler. -/
protected abbrev Orientation.enumList : List Orientation := [Orientation.negative, Orientation.positive]

protected theorem Orientation.enumList_getElem?_ctorIdx_eq (x : Orientation) :
    Orientation.enumList[Orientation.ctorIdx x]? = some x := by
  cases x <;> rfl

protected theorem Orientation.enumList_nodup : Orientation.enumList.Nodup := by
  apply List.Nodup.of_map Orientation.ctorIdx
  have h : List.map Orientation.ctorIdx Orientation.enumList = List.range 2 := rfl
  exact h ▸ List.nodup_range

instance : Fintype Orientation where
  elems := Finset.mk Orientation.enumList Orientation.enumList_nodup
  complete := by
    intro x
    cases x <;> decide

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
