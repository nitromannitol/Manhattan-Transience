import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Distributions.Uniform

/-!
# Sites, directed lines, and the fair-coin environment

The paper records a line orientation redundantly as `omega (z,i)`, subject
to independence of the `i`th coordinate.  We use the equivalent irredundant
index `(i,k)`, where `k` is the transverse coordinate.

Paper: `manuscript.tex:167-184`.
-/

open MeasureTheory ProbabilityTheory

namespace Manhattan

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

@[simp] theorem Orientation.sign_negative : Orientation.negative.sign = -1 := rfl

@[simp] theorem Orientation.sign_positive : Orientation.positive.sign = 1 := rfl

theorem Orientation.sign_eq_neg_one_or_one (o : Orientation) : o.sign = -1 ∨ o.sign = 1 := by
  cases o <;> simp

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

/-- Evaluation of the environment at each line is an independent family. -/
theorem iIndepFun_orientation :
    iIndepFun (fun l : LineIndex => fun ω : Environment => ω l) environmentLaw := by
  simpa only [environmentLaw] using
    (iIndepFun_infinitePi (P := fun _ : LineIndex => fairCoin) (fun _ => measurable_id))

/-- Each environment coordinate preserves the fair-coin law. -/
theorem measurePreserving_orientation (l : LineIndex) :
    MeasurePreserving (fun ω : Environment => ω l) environmentLaw fairCoin := by
  exact measurePreserving_eval_infinitePi (fun _ : LineIndex => fairCoin) l

/-- Translation of line indices by a lattice vector. -/
def lineTranslation (x : Site) : LineIndex ≃ LineIndex where
  toFun l := (l.1, l.2 + transverseCoordinate x l.1)
  invFun l := (l.1, l.2 - transverseCoordinate x l.1)
  left_inv l := by cases l.1 <;> simp [transverseCoordinate]
  right_inv l := by cases l.1 <;> simp [transverseCoordinate]

/-- The translated environment `tau_x omega`, viewed from the site `x`. -/
def translateEnvironment (x : Site) (ω : Environment) : Environment :=
  fun l => ω (lineTranslation x l)

theorem measurable_translateEnvironment (x : Site) : Measurable (translateEnvironment x) := by
  rw [measurable_pi_iff]
  exact fun l => measurable_pi_apply (lineTranslation x l)

/-- The product fair-coin law is invariant under lattice translations. -/
theorem measurePreserving_translateEnvironment (x : Site) :
    MeasurePreserving (translateEnvironment x) environmentLaw environmentLaw := by
  refine ⟨measurable_translateEnvironment x, ?_⟩
  have h := Measure.infinitePi_map_piCongrLeft
    (μ := fun _ : LineIndex => fairCoin) (X := fun _ : LineIndex => Orientation)
    (lineTranslation x).symm
  have hfun : translateEnvironment x =
      MeasurableEquiv.piCongrLeft (fun _ : LineIndex => Orientation)
        (lineTranslation x).symm := by
    funext ω l
    simp [translateEnvironment, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]
  simpa only [environmentLaw, hfun] using h

@[simp] theorem translateEnvironment_zero (ω : Environment) :
    translateEnvironment 0 ω = ω := by
  funext l
  rcases l with ⟨i, k⟩
  cases i <;> simp [translateEnvironment, lineTranslation, transverseCoordinate]

theorem translateEnvironment_add (x y : Site) (ω : Environment) :
    translateEnvironment (x + y) ω =
      translateEnvironment y (translateEnvironment x ω) := by
  funext l
  rcases l with ⟨i, k⟩
  cases i <;> simp [translateEnvironment, lineTranslation, transverseCoordinate] <;> ac_rfl

/-- The line through `z`, after translating the environment by `x`, is the
line through `x + z` before translation. -/
theorem lineTranslation_lineAt (x z : Site) (i : Axis) :
    lineTranslation x (lineAt z i) = lineAt (x + z) i := by
  cases i <;> simp [lineTranslation, lineAt, transverseCoordinate, add_comm]

/-- Translation covariance of a single directed edge. -/
theorem directedNeighbor_translate (x z : Site) (ω : Environment) (i : Axis) :
    directedNeighbor ω (x + z) i =
      x + directedNeighbor (translateEnvironment x ω) z i := by
  cases i <;>
    simp [directedNeighbor, translateEnvironment, lineTranslation, lineAt,
      transverseCoordinate, basisStep, add_assoc, add_comm]

end Manhattan
