import Manhattan.Estimates.DegreeOne
import Manhattan.Walsh.LowDegreeSectors

/-!
# The concrete lowering operator `D*` in Finset Walsh coordinates

`A_p = D - D*` is skew-adjoint, so for every `x` in `Manhattan.WalshL2` the
Walsh coefficient of `D* x` at a Finset index `S` is the inner product
`⟪A_p (walshL2 S), x⟫`.  This file computes that pairing from the actual
concrete operator: one signed lattice step along each axis followed by the
toggle of the line of that type through the origin.  No factorial and no
tuple normalization is imported; every constant below is the one forced by
the literal Finset isometry (17) of `Manhattan.Walsh.Coefficients`.

Specializing to `S = ∅` gives the first formula of (D1),
`manuscript.tex:827-840`, and then `D_0^* f_p = -b_p` of Lemma 4.1(a),
`manuscript.tex:915-920`.

Paper: `manuscript.tex:719-740`, `manuscript.tex:793-840`,
`manuscript.tex:1176-1205`.
-/

open ComplexConjugate InnerProductSpace MeasureTheory
open scoped BigOperators ComplexConjugate

namespace Manhattan.Glue

noncomputable section

/-- The Walsh coefficient of an arbitrary `L²` vector at one Finset index. -/
def walshCoefficientAt (x : WalshL2) (S : Finset LineIndex) : ℂ :=
  inner ℂ (walshL2 S) x

/-- On a finite Walsh polynomial the coefficient map is the literal
coefficient: this is (17) with no factorial. -/
@[simp] theorem walshCoefficientAt_walshSynthesis (c : WalshCoefficient)
    (S : Finset LineIndex) :
    walshCoefficientAt (walshSynthesis c) S = c S := by
  have hS : walshSynthesis (Finsupp.single S 1) = walshL2 S := by simp
  rw [walshCoefficientAt, ← hS, inner_walshSynthesis, walshCoefficientInner,
    Finsupp.sum_single_index (by simp)]
  simp

/-- The `S`-coefficient of `D* x`.  Because `A_p` is skew-adjoint and
`A_p = D - D*`, this is the inner product of `x` against the raising image of
the Walsh character `S`. -/
def loweringCoefficient (p : Fin 2 → ℝ) (x : WalshL2) (S : Finset LineIndex) : ℂ :=
  inner ℂ (concreteFiberA p (walshL2 S)) x

/-- The defining adjoint identity: `(D* x)_S = -(A_p x)_S`. -/
theorem loweringCoefficient_eq_neg_inner (p : Fin 2 → ℝ) (x : WalshL2)
    (S : Finset LineIndex) :
    loweringCoefficient p x S = -inner ℂ (walshL2 S) (concreteFiberA p x) := by
  rw [loweringCoefficient, ← (concreteFiberA p).adjoint_inner_left,
    concreteFiberA_skewAdjoint, ContinuousLinearMap.neg_apply, inner_neg_left]
  simp

private theorem conj_half_exp (t : ℝ) :
    conj ((2 : ℂ)⁻¹ * Complex.exp (Complex.I * t)) =
      (2 : ℂ)⁻¹ * Complex.exp (-Complex.I * t) := by
  rw [map_mul, map_inv₀, map_ofNat, ← Complex.exp_conj]
  norm_num

private theorem conj_half_exp_neg (t : ℝ) :
    conj ((2 : ℂ)⁻¹ * Complex.exp (-Complex.I * t)) =
      (2 : ℂ)⁻¹ * Complex.exp (Complex.I * t) := by
  rw [map_mul, map_inv₀, map_ofNat, ← Complex.exp_conj]
  norm_num

/-- The concrete skew fiber on one Walsh character, written as the explicit
four-term combination of Walsh characters. -/
theorem concreteFiberA_walshL2_expand (p : Fin 2 → ℝ) (S : Finset LineIndex) :
    concreteFiberA p (walshL2 S) =
      ∑ i : Fin 2,
        (((2 : ℂ)⁻¹ * Complex.exp (Complex.I * p i)) •
            walshL2 (toggleOriginWalshIndex i
              (translateWalshIndex (Operator.axisVector i) S)) -
          ((2 : ℂ)⁻¹ * Complex.exp (-Complex.I * p i)) •
            walshL2 (toggleOriginWalshIndex i
              (translateWalshIndex (-Operator.axisVector i) S))) := by
  rw [concreteFiberA_walshL2, fiberASpatialCoefficient, walshSynthesis_smul,
    walshSynthesis_sum Finset.univ]
  simp only [walshSynthesis_sub, walshSynthesis_single, Finset.smul_sum,
    smul_sub, smul_smul]

/-- **Lemma 5.1, adjoint side.**  The Walsh coefficients of `D* x` in the
Finset isometry.  Each axis contributes the two signed lattice steps, with
the phase conjugated by the adjoint. -/
theorem loweringCoefficient_eq (p : Fin 2 → ℝ) (x : WalshL2)
    (S : Finset LineIndex) :
    loweringCoefficient p x S =
      ∑ i : Fin 2,
        (((2 : ℂ)⁻¹ * Complex.exp (-Complex.I * p i)) *
            walshCoefficientAt x (toggleOriginWalshIndex i
              (translateWalshIndex (Operator.axisVector i) S)) -
          ((2 : ℂ)⁻¹ * Complex.exp (Complex.I * p i)) *
            walshCoefficientAt x (toggleOriginWalshIndex i
              (translateWalshIndex (-Operator.axisVector i) S))) := by
  rw [loweringCoefficient, concreteFiberA_walshL2_expand, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_sub_left, inner_smul_left, inner_smul_left, conj_half_exp,
    conj_half_exp_neg]
  rfl

/-- The same formula on a finite Walsh polynomial. -/
theorem loweringCoefficient_walshSynthesis (p : Fin 2 → ℝ)
    (c : WalshCoefficient) (S : Finset LineIndex) :
    loweringCoefficient p (walshSynthesis c) S =
      ∑ i : Fin 2,
        (((2 : ℂ)⁻¹ * Complex.exp (-Complex.I * p i)) *
            c (toggleOriginWalshIndex i
              (translateWalshIndex (Operator.axisVector i) S)) -
          ((2 : ℂ)⁻¹ * Complex.exp (Complex.I * p i)) *
            c (toggleOriginWalshIndex i
              (translateWalshIndex (-Operator.axisVector i) S))) := by
  simpa using loweringCoefficient_eq p (walshSynthesis c) S

/-- `2⁻¹(e^{-it} - e^{it}) = -i sin t`, the phase difference produced by the
adjoint of one signed lattice step. -/
theorem half_exp_neg_sub_half_exp (t : ℝ) :
    (2 : ℂ)⁻¹ * Complex.exp (-Complex.I * t) -
        (2 : ℂ)⁻¹ * Complex.exp (Complex.I * t) =
      -(Complex.I * (Real.sin t : ℂ)) := by
  have h := half_exp_I_sub_exp_neg_I t
  linear_combination -h

/-- The degree-zero lowering coefficient: only the two lines through the
origin contribute, each with the phase `-i sin p`. -/
theorem loweringCoefficient_empty (p : Fin 2 → ℝ) (x : WalshL2) :
    loweringCoefficient p x ∅ =
      -(Complex.I * (Real.sin (p 0) : ℂ)) *
          walshCoefficientAt x {(Axis.horizontal, 0)} +
        -(Complex.I * (Real.sin (p 1) : ℂ)) *
          walshCoefficientAt x {(Axis.vertical, 0)} := by
  rw [loweringCoefficient_eq, Fin.sum_univ_two]
  simp only [translateWalshIndex_empty, toggleOriginWalshIndex_empty,
    originLine, finAxis_zero, finAxis_one]
  linear_combination
    (walshCoefficientAt x {(Axis.horizontal, 0)}) * half_exp_neg_sub_half_exp (p 0) +
      (walshCoefficientAt x {(Axis.vertical, 0)}) * half_exp_neg_sub_half_exp (p 1)

/-- **(D1), first formula, on the complete degree-one row sector.**  Only the
zero line frequency survives, so `D_0^*` reads off the zero Fourier
coefficient. -/
theorem dStarZero_axisDegreeOne (p : Fin 2 → ℝ) (c : RowLineCoefficient) :
    loweringCoefficient p (axisDegreeOneSynthesis Axis.horizontal c) ∅ =
      -(Complex.I * (Real.sin (p 0) : ℂ)) * c 0 := by
  rw [loweringCoefficient_empty, walshCoefficientAt, walshCoefficientAt,
    inner_axisDegreeOneSynthesis,
    inner_axisDegreeOneSynthesis_of_ne Axis.horizontal Axis.vertical (by decide)]
  ring

/-- **(D1), first formula, in the paper's normalized torus integral**:
`D_0^* f = -i sin(p₁) ∫_𝕋 f dm` (`manuscript.tex:827-840`).  The factor
`(2π)⁻¹` is the normalization of `dm`; no factorial appears. -/
theorem dStarZero_degreeOneRealFrequency (p : Fin 2 → ℝ) (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Set.Ioc (-Real.pi) Real.pi))) :
    loweringCoefficient p
        (degreeOneRealFrequencySynthesis Axis.horizontal f hf) ∅ =
      -(Complex.I * (Real.sin (p 0) : ℂ)) * Estimates.torusIntegral f := by
  rw [degreeOneRealFrequencySynthesis, degreeOneFrequencySynthesis]
  change loweringCoefficient p
      (axisDegreeOneSynthesis Axis.horizontal
        (fourierBasis.repr (realTorusL2 f hf))) ∅ = _
  rw [dStarZero_axisDegreeOne, fourierBasis_repr_realTorusL2_zero]
  rw [Estimates.torusIntegral, Estimates.torus, Complex.real_smul]

private theorem sign_mul_self (t : ℝ) : Real.sign t * t = |t| := by
  rcases lt_trichotomy t 0 with ht | ht | ht
  · rw [Real.sign_of_neg ht, abs_of_neg ht]; ring
  · simp [ht]
  · rw [Real.sign_of_pos ht, abs_of_pos ht]; ring

/-- **Lemma 4.1(a) of the manuscript, exactly**: with the degree-one
coefficient `f_p` of (eq:f), `D_0^* f_p = -b_p`
(`manuscript.tex:915-920`). -/
theorem dStarZero_degreeOneCoefficient_eq_neg_normalization
    (q : Estimates.Parameters) (p : Fin 2 → ℝ)
    (hf : MemLp (Estimates.degreeOneCoefficient q (p 0)) 2
      (volume.restrict (Set.Ioc (-Real.pi) Real.pi))) :
    loweringCoefficient p
        (degreeOneRealFrequencySynthesis Axis.horizontal
          (Estimates.degreeOneCoefficient q (p 0)) hf) ∅ =
      -(Estimates.degreeOneNormalization q (p 0) : ℂ) := by
  classical
  have hsplit : Estimates.degreeOneCoefficient q (p 0) =
      fun r => (-Complex.I * (Real.sign (Real.sin (p 0)) : ℂ)) *
        (((if r ∈ q.supportInterval |p 0| then (Real.sin r)⁻¹ else 0 : ℝ)) : ℂ) := by
    funext r
    unfold Estimates.degreeOneCoefficient
    by_cases hr : r ∈ q.supportInterval |p 0| <;>
      simp [hr, div_eq_mul_inv]
  rw [dStarZero_degreeOneRealFrequency, hsplit,
    Estimates.degreeOneNormalization]
  simp only [Estimates.torusIntegral, Estimates.torus, smul_eq_mul,
    Complex.real_smul, integral_const_mul]
  rw [← sign_mul_self (Real.sin (p 0))]
  push_cast
  rw [integral_complex_ofReal]
  linear_combination (Complex.sin ((p 0 : ℝ) : ℂ) * (2 * (Real.pi : ℂ))⁻¹ *
      ((Real.sign (Real.sin (p 0)) : ℝ) : ℂ) *
      (((∫ r in Set.Ioc (-Real.pi) Real.pi,
        (if r ∈ q.supportInterval |p 0| then (Real.sin r)⁻¹ else 0) : ℝ) : ℝ) : ℂ)) *
    Complex.I_mul_I

/-- `D₂*` is genuinely the adjoint of the raising operator `D₂`.  On a
degree-three vector the signed lowering part of `A_p (walshL2 S)` is
orthogonal, so the pairing sees only the raising part. -/
theorem loweringCoefficient_type112_eq_inner_raising (p : Fin 2 → ℝ)
    (c : ℓ²(Type112Index, ℂ)) (S : Finset LineIndex) (hS : S.card = 2) :
    loweringCoefficient p (type112WalshSynthesis c) S =
      inner ℂ (walshSynthesis (fiberDRaisingSpatialCoefficient p S))
        (type112WalshSynthesis c) := by
  rw [loweringCoefficient, concreteFiberA_walshL2_eq_D_sub_DStar p S,
    inner_sub_left]
  have hzero :
      inner ℂ (walshSynthesis (fiberDStarLoweringSpatialCoefficient p S))
        (type112WalshSynthesis c) = 0 := by
    rw [inner_walshSynthesis_type112WalshSynthesis]
    refine Finset.sum_eq_zero fun T hT => ?_
    have hcard :=
      isWalshDegree_fiberDStarLoweringSpatialCoefficient p S hS T hT
    have hnot : ¬ IsType112Index T := by
      intro h112
      rw [h112.1] at hcard
      omega
    simp [type112CoefficientAt, hnot]
  rw [hzero, sub_zero]

/-- Bridge to the two-row lowering coefficient. -/
theorem type112DStarTwoRow_eq_loweringCoefficient (p : Fin 2 → ℝ)
    (c : ℓ²(Type112Index, ℂ)) (T : Type11Index) :
    type112DStarTwoRow p c T = loweringCoefficient p (type112WalshSynthesis c) T.1 :=
  type112DStarTwoRow_apply p c T

/-- Bridge to the mixed lowering coefficient. -/
theorem type112DStarMixed_eq_loweringCoefficient (p : Fin 2 → ℝ)
    (c : ℓ²(Type112Index, ℂ)) (T : Type12Index) :
    type112DStarMixed p c T = loweringCoefficient p (type112WalshSynthesis c) T.1 :=
  type112DStarMixed_apply p c T

end

end Manhattan.Glue
