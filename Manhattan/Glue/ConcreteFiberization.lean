import Manhattan.Glue.VectorFourier

/-!
# Concrete joint-generator fiberization

This file writes the position/environment generator on complete
Fourier--Walsh coefficient spaces. Its elementary shift is precisely
`F(τ_x ω, z+x)`, and `jointPositionFourier` conjugates the resulting
bounded generator to the frequency-side operator.

Paper: `manuscript.tex:555-583`.
-/

noncomputable section

open UnitAddTorus
open scoped BigOperators

namespace Manhattan.Glue

/-- Translation of Finset Walsh indices as an equivalence. -/
def translateWalshIndexEquiv (x : Operator.Lattice) :
    Finset LineIndex ≃ Finset LineIndex :=
  (lineTranslation (latticeToSite x)).finsetCongr

@[simp] theorem translateWalshIndexEquiv_apply (x : Operator.Lattice)
    (S : Finset LineIndex) :
    translateWalshIndexEquiv x S = translateWalshIndex x S := rfl

/-- Toggling an origin line is an involutive equivalence of Walsh indices. -/
def toggleOriginWalshIndexEquiv (i : Fin 2) :
    Finset LineIndex ≃ Finset LineIndex where
  toFun := toggleOriginWalshIndex i
  invFun := toggleOriginWalshIndex i
  left_inv S := by
    ext l
    simp only [toggleOriginWalshIndex, Finset.mem_symmDiff,
      Finset.mem_singleton]
    tauto
  right_inv S := by
    ext l
    simp only [toggleOriginWalshIndex, Finset.mem_symmDiff,
      Finset.mem_singleton]
    tauto

@[simp] theorem toggleOriginWalshIndexEquiv_apply (i : Fin 2)
    (S : Finset LineIndex) :
    toggleOriginWalshIndexEquiv i S = toggleOriginWalshIndex i S := rfl

/-- On position coefficients, replace `F(z)` by `F(z+x)`. -/
noncomputable def positionArgumentShift (x : Operator.Lattice) :
    Operator.PositionL2 ≃ₗᵢ[ℂ] Operator.PositionL2 :=
  l2CongrLeft (Equiv.addRight (-x))

@[simp] theorem positionArgumentShift_apply (x : Operator.Lattice)
    (f : Operator.PositionL2) (z : Operator.Lattice) :
    positionArgumentShift x f z = f (z + x) := by
  simp [positionArgumentShift]

/-- Simultaneously apply `τ_x` in the environment and replace `z` by
`z+x`, the elementary operation in (7). -/
noncomputable def jointTranslatedStep (x : Operator.Lattice) :
    JointPositionL2 ≃ₗᵢ[ℂ] JointPositionL2 :=
  (l2CongrLeft (translateWalshIndexEquiv x)).trans
    (l2CongrRight (positionArgumentShift x))

/-- Multiplication by the origin sign in Walsh coordinates. -/
noncomputable def jointOriginSign (i : Fin 2) :
    JointPositionL2 ≃ₗᵢ[ℂ] JointPositionL2 :=
  l2CongrLeft (toggleOriginWalshIndexEquiv i)

/-- The symmetric joint-generator summand in direction `i`. -/
noncomputable def jointSymmetricTerm (i : Fin 2) :
    JointPositionL2 →L[ℂ] JointPositionL2 :=
  (jointTranslatedStep (Operator.axisVector i)).toLinearIsometry.toContinuousLinearMap +
    (jointTranslatedStep (-Operator.axisVector i)).toLinearIsometry.toContinuousLinearMap -
    (2 : ℂ) • ContinuousLinearMap.id ℂ JointPositionL2

/-- The antisymmetric joint-generator summand in direction `i`. -/
noncomputable def jointSkewTerm (i : Fin 2) :
    JointPositionL2 →L[ℂ] JointPositionL2 :=
  (jointOriginSign i).toLinearIsometry.toContinuousLinearMap ∘L
    ((jointTranslatedStep (Operator.axisVector i)).toLinearIsometry.toContinuousLinearMap -
      (jointTranslatedStep (-Operator.axisVector i)).toLinearIsometry.toContinuousLinearMap)

/-- Equation (7), after splitting the two values of each origin sign as in
the proof of Proposition 2.1. -/
noncomputable def concreteJointGenerator :
    JointPositionL2 →L[ℂ] JointPositionL2 :=
  (2 : ℂ)⁻¹ • ∑ i : Fin 2, (jointSymmetricTerm i + jointSkewTerm i)

/-- The frequency-side joint operator is the genuine unitary conjugate of
the concrete joint generator. -/
noncomputable def concreteJointFiberOperator :
    JointFrequencyL2 →L[ℂ] JointFrequencyL2 :=
  jointPositionFourier.toLinearIsometry.toContinuousLinearMap ∘L
    concreteJointGenerator ∘L
      jointPositionFourier.symm.toLinearIsometry.toContinuousLinearMap

/-- The concrete `JointFiberization` instance. -/
noncomputable def concreteJointFiberization :
    Operator.JointFiberization WalshL2 JointPositionL2 JointFrequencyL2 where
  environment := concreteFiberEnvironment
  transform := jointPositionFourier
  jointGenerator := concreteJointGenerator
  fiberOperator := concreteJointFiberOperator
  transformed_generator F := by
    simp [concreteJointFiberOperator]

/-- The requested true intertwining statement for the concrete certificate. -/
theorem concreteJointGenerator_fiberizes (F : JointPositionL2) :
    jointPositionFourier (concreteJointGenerator F) =
      concreteJointFiberOperator (jointPositionFourier F) := by
  exact concreteJointFiberization.transformed_generator F

/-- Equivalent conjugation identity for the concrete joint generator. -/
theorem concreteJointGenerator_eq_fourier_conjugate (F : JointPositionL2) :
    concreteJointGenerator F =
      jointPositionFourier.symm
        (concreteJointFiberOperator (jointPositionFourier F)) := by
  exact jointGenerator_eq_transform_symm concreteJointFiberization F

set_option maxHeartbeats 800000 in
/-- The elementary joint shift sends `(S,z)` to
`(τ_x S,z-x)`, exactly the coefficient action of `F(τ_xω,z+x)`. -/
@[simp] theorem jointTranslatedStep_single (x : Operator.Lattice)
    (S : Finset LineIndex) (z : Operator.Lattice) :
    jointTranslatedStep x (lp.single 2 S (lp.single 2 z (1 : ℂ))) =
      lp.single 2 (translateWalshIndex x S)
        (lp.single 2 (z - x) (1 : ℂ)) := by
  apply lp.ext
  funext T
  by_cases hT : T = translateWalshIndex x S
  · subst T
    have hinv : (translateWalshIndexEquiv x).symm
        (translateWalshIndex x S) = S := by
      rw [← translateWalshIndexEquiv_apply]
      exact (translateWalshIndexEquiv x).symm_apply_apply S
    apply lp.ext
    funext w
    simp only [jointTranslatedStep, LinearIsometryEquiv.trans_apply,
      l2CongrLeft_apply, l2CongrRight_apply, positionArgumentShift_apply]
    rw [hinv]
    simp only [lp.single_apply]
    by_cases hw : w = z - x
    · subst w
      simp
    · have hwx : w + x ≠ z := by
        intro heq
        apply hw
        exact eq_sub_of_add_eq heq
      simp [lp.single_apply, hw, hwx]
  · have hinv : (translateWalshIndexEquiv x).symm T ≠ S := by
      intro heq
      apply hT
      calc
        T = translateWalshIndexEquiv x
            ((translateWalshIndexEquiv x).symm T) :=
          ((translateWalshIndexEquiv x).apply_symm_apply T).symm
        _ = translateWalshIndexEquiv x S := congrArg _ heq
        _ = translateWalshIndex x S := translateWalshIndexEquiv_apply x S
    simp only [jointTranslatedStep, LinearIsometryEquiv.trans_apply,
      l2CongrLeft_apply, l2CongrRight_apply]
    have hzero :
        ((lp.single 2 S (lp.single 2 z (1 : ℂ))) : JointPositionL2)
            ((translateWalshIndexEquiv x).symm T) = 0 := by
      simp [lp.single_apply, hinv]
    rw [hzero, map_zero]
    simp [lp.single_apply, hT]

/-- After the negative-phase transform, the elementary shift changes the
Fourier monomial from `-z` to `-(z-x)=-z+x`, hence has the paper's positive
shift phase. -/
@[simp] theorem jointPositionFourier_jointTranslatedStep_single
    (x : Operator.Lattice) (S : Finset LineIndex) (z : Operator.Lattice) :
    jointPositionFourier
        (jointTranslatedStep x
          (lp.single 2 S (lp.single 2 z (1 : ℂ)))) =
      lp.single 2 (translateWalshIndex x S)
        (mFourierLp 2 (-(z - x))) := by
  rw [jointTranslatedStep_single, jointPositionFourier_single]

end Manhattan.Glue
