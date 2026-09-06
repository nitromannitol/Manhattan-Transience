import Manhattan.Operator.Variational
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.Complex.Trigonometric

/-!
# Fourier transform in position and certified fiber operators

The scalar position transform uses Mathlib's multivariate Fourier Hilbert
basis. The environment-side transform remains abstract here. Its
operator family carries the exact formulas and the elementary Hilbert-space
properties required by Proposition 2.1; a concrete probability-space model
must supply this certificate.

Paper: manuscript.tex:543-608.
-/

noncomputable section

open ComplexConjugate InnerProductSpace MeasureTheory RCLike UnitAddTorus
open scoped BigOperators ComplexConjugate InnerProduct

namespace Manhattan.Operator

/-- The lattice used for position Fourier transform. -/
abbrev Lattice := Fin 2 → ℤ

/-- Scalar square-summable functions of position. -/
abbrev PositionL2 := ℓ²(Lattice, ℂ)

/-- Plancherel Fourier transform from ell^2(Z^2) to Mathlib's normalized
unit two-torus. Its inferred codomain deliberately retains the measure-space
instance used by mFourierBasis. -/
def positionFourier :=
  (mFourierBasis (d := Fin 2)).repr.symm

theorem positionFourier_norm (f : PositionL2) : ‖positionFourier f‖ = ‖f‖ :=
  positionFourier.norm_map f

/-- Fourier image of a lattice delta; this fixes sign and normalization. -/
theorem positionFourier_single (z : Lattice) :
    positionFourier (lp.single 2 z (1 : ℂ)) = mFourierLp 2 z := by
  simpa only [positionFourier, coe_mFourierBasis] using
    (mFourierBasis (d := Fin 2)).repr_symm_single z

/-- The ith coordinate vector in Z^2. -/
def axisVector (i : Fin 2) : Lattice := Pi.single i 1

/-- -- INTERFACE: certified abstract form of Proposition 2.1.
The formula fields prevent a concrete model from hiding a different
operator behind the certificate. The five property fields are the precise
elementary unitary-shift obligations to be discharged when the probability
space is connected. -/
structure FiberEnvironment (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] where
  /-- The unitary translation of the environment by a lattice vector. -/
  shift : Lattice → E →L[ℂ] E
  /-- Multiplication by the orientation sign of each axis. -/
  omega : Fin 2 → E →L[ℂ] E
  /-- The symmetric part `S_p` of the fibered generator. -/
  fiberS : (Fin 2 → ℝ) → E →L[ℂ] E
  /-- The skew part `A_p` of the fibered generator. -/
  fiberA : (Fin 2 → ℝ) → E →L[ℂ] E
  fiberS_formula : ∀ p,
    fiberS p = (2 : ℂ)⁻¹ • ∑ i,
      (Complex.exp (Complex.I * p i) • shift (axisVector i) +
       Complex.exp (-Complex.I * p i) • shift (-axisVector i) -
       (2 : ℂ) • ContinuousLinearMap.id ℂ E)
  fiberA_formula : ∀ p,
    fiberA p = (2 : ℂ)⁻¹ • ∑ i, omega i ∘L
      (Complex.exp (Complex.I * p i) • shift (axisVector i) -
       Complex.exp (-Complex.I * p i) • shift (-axisVector i))
  fiberS_selfAdjoint_spec : ∀ p, IsSelfAdjoint (fiberS p)
  fiberS_nonpositive_spec : ∀ p x, re ⟪fiberS p x, x⟫_ℂ ≤ 0
  fiberS_norm_le_spec : ∀ p, ‖fiberS p‖ ≤ 4
  fiberA_skewAdjoint_spec : ∀ p, (fiberA p)† = -fiberA p
  fiberA_norm_le_spec : ∀ p, ‖fiberA p‖ ≤ 2

namespace FiberEnvironment

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (D : FiberEnvironment E)

/-- Fiber generator G_p = S_p + A_p. -/
def fiberGenerator (p : Fin 2 → ℝ) : E →L[ℂ] E :=
  D.fiberS p + D.fiberA p

theorem fiberS_eq_formula (p : Fin 2 → ℝ) :
    D.fiberS p = (2 : ℂ)⁻¹ • ∑ i,
      (Complex.exp (Complex.I * p i) • D.shift (axisVector i) +
       Complex.exp (-Complex.I * p i) • D.shift (-axisVector i) -
       (2 : ℂ) • ContinuousLinearMap.id ℂ E) :=
  D.fiberS_formula p

theorem fiberA_eq_formula (p : Fin 2 → ℝ) :
    D.fiberA p = (2 : ℂ)⁻¹ • ∑ i, D.omega i ∘L
      (Complex.exp (Complex.I * p i) • D.shift (axisVector i) -
       Complex.exp (-Complex.I * p i) • D.shift (-axisVector i)) :=
  D.fiberA_formula p

theorem fiberS_selfAdjoint (p : Fin 2 → ℝ) : IsSelfAdjoint (D.fiberS p) :=
  D.fiberS_selfAdjoint_spec p

theorem fiberS_nonpositive (p : Fin 2 → ℝ) (x : E) :
    re ⟪D.fiberS p x, x⟫_ℂ ≤ 0 :=
  D.fiberS_nonpositive_spec p x

theorem fiberS_norm_le (p : Fin 2 → ℝ) : ‖D.fiberS p‖ ≤ 4 :=
  D.fiberS_norm_le_spec p

theorem fiberA_skewAdjoint (p : Fin 2 → ℝ) : (D.fiberA p)† = -D.fiberA p :=
  D.fiberA_skewAdjoint_spec p

theorem fiberA_norm_le (p : Fin 2 → ℝ) : ‖D.fiberA p‖ ≤ 2 :=
  D.fiberA_norm_le_spec p

/-- Proposition 2.1's operator assertions packaged for the variational layer. -/
def dissipativeSkewPair (p : Fin 2 → ℝ) : DissipativeSkewPair E where
  S := D.fiberS p
  A := D.fiberA p
  selfAdjoint_S := D.fiberS_selfAdjoint p
  nonpositive_S := D.fiberS_nonpositive p
  skewAdjoint_A := D.fiberA_skewAdjoint p

end FiberEnvironment

/-- -- INTERFACE: vector-valued Fourier fiberization required from the
concrete environment files. -/
structure JointFiberization (E J K : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] [NormedAddCommGroup J]
    [InnerProductSpace ℂ J] [CompleteSpace J] [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] where
  /-- The fibered environment being transformed. -/
  environment : FiberEnvironment E
  /-- The vector-valued Fourier isometry. -/
  transform : J ≃ₗᵢ[ℂ] K
  /-- The generator on the joint space, before the transform. -/
  jointGenerator : J →L[ℂ] J
  /-- The operator that the transform conjugates the generator into. -/
  fiberOperator : K →L[ℂ] K
  transformed_generator : ∀ F : J,
    transform (jointGenerator F) = fiberOperator (transform F)

end Manhattan.Operator
