import Manhattan.Walsh.Coefficients
import Mathlib.Analysis.Fourier.AddCircle

/-!
# Fourier series in a single line index

Equation (20) takes Fourier series in the transverse integer coordinate of
each directed line.  With Finset-indexed higher chaoses there is no canonical
ordering of several frequencies.  This module therefore records the clean,
ordering-free degree-one transform and the embedding of one line frequency
into the two-dimensional torus; higher-degree sector transforms are left to
the explicit low-degree modules that choose an axis pattern.

Paper: `manuscript.tex:743-750`.
-/

open MeasureTheory

namespace Manhattan

/-- The paper's torus period. -/
noncomputable def torusPeriod : ℝ := 2 * Real.pi

instance torusPeriodPositive : Fact (0 < torusPeriod) :=
  ⟨mul_pos (by norm_num) Real.pi_pos⟩

/-- One Fourier frequency transverse to a line, retaining its axis tag. -/
abbrev LineFrequency := Axis × AddCircle torusPeriod

/-- A two-dimensional torus frequency, with coordinates labelled by axes. -/
abbrev TorusFrequency := Axis → AddCircle torusPeriod

/-- Embed a line frequency into the two-dimensional frequency space.  A
horizontal line is indexed by its vertical coordinate and conversely. -/
def embedLineFrequency (q : LineFrequency) : TorusFrequency := fun i =>
  match q.1, i with
  | .horizontal, .horizontal => 0
  | .horizontal, .vertical => q.2
  | .vertical, .horizontal => q.2
  | .vertical, .vertical => 0

@[simp] theorem embedLineFrequency_same (q : LineFrequency) :
    embedLineFrequency q q.1 = 0 := by
  rcases q with ⟨i, q⟩
  cases i <;> rfl

/-- Square-summable coefficients in the transverse coordinate, one copy for
each axis. -/
abbrev DegreeOneLineCoefficient := Axis → lp (fun _ : ℤ => ℂ) 2

/-- Equation (20) in degree one: Fourier-series synthesis in each line index.
This is a linear isometric equivalence in each axis sector. -/
noncomputable def degreeOneLineFourier (f : DegreeOneLineCoefficient) (i : Axis) :
    Lp ℂ 2 (AddCircle.haarAddCircle : Measure (AddCircle torusPeriod)) :=
  (@fourierBasis torusPeriod torusPeriodPositive).repr.symm (f i)

/-- Plancherel for the clean degree-one line transform. -/
theorem norm_degreeOneLineFourier (f : DegreeOneLineCoefficient) (i : Axis) :
    ‖degreeOneLineFourier f i‖ = ‖f i‖ := by
  simp [degreeOneLineFourier]

end Manhattan
