import Manhattan.Operator.Fourier

/-!
# Joint-generator fiberization

The operator part deliberately packages the model-specific Fourier transform
as a `JointFiberization` certificate. These lemmas expose its intertwining
identity and conjugation consequence without adding a second transform API.

Paper: `manuscript.tex:555-597`.
-/

noncomputable section

namespace Manhattan.Glue

open Manhattan.Operator

variable {E J K : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The joint generator is intertwined with its fiber operator by the
position Fourier transform carried by the abstract certificate. -/
theorem jointGenerator_fiberizes (D : JointFiberization E J K) (F : J) :
    D.transform (D.jointGenerator F) = D.fiberOperator (D.transform F) :=
  D.transformed_generator F

/-- Equivalent conjugation form of `jointGenerator_fiberizes`. -/
theorem jointGenerator_eq_transform_symm (D : JointFiberization E J K) (F : J) :
    D.jointGenerator F = D.transform.symm (D.fiberOperator (D.transform F)) := by
  rw [← jointGenerator_fiberizes D F]
  exact (D.transform.symm_apply_apply (D.jointGenerator F)).symm

end Manhattan.Glue
