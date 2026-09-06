import Manhattan.Model.FiberInstance
import Manhattan.Operator.Frequency
import Manhattan.Walsh.LowDegree

/-!
# Concrete fiber action in Finset Walsh coordinates

The formulas here are the spatial-coefficient form of (18) and Lemma 5.1.
They identify the actual `concreteFiberS` and `concreteFiberA` actions, rather
than introducing a scalar operator with the desired formula by definition.

Paper: `manuscript.tex:719-758`, `manuscript.tex:793-822`, and
`manuscript.tex:1179-1205`.
-/

open ComplexConjugate InnerProductSpace RCLike
open MeasureTheory
open scoped BigOperators ComplexConjugate InnerProduct symmDiff

namespace Manhattan

noncomputable section

/-- Translation of a Walsh index by a lattice vector. -/
def translateWalshIndex (x : Operator.Lattice) (S : Finset LineIndex) :
    Finset LineIndex :=
  Finset.map (lineTranslation (latticeToSite x)).toEmbedding S

/-- Toggle the line through the origin in direction `i`. -/
def toggleOriginWalshIndex (i : Fin 2) (S : Finset LineIndex) :
    Finset LineIndex :=
  S ∆ {originLine i}

/-- Translation does not change Walsh degree. -/
@[simp] theorem card_translateWalshIndex (x : Operator.Lattice)
    (S : Finset LineIndex) :
    (translateWalshIndex x S).card = S.card := by
  exact Finset.card_map (lineTranslation (latticeToSite x)).toEmbedding

/-- Toggling a coordinate is insertion in the raising case and erasure in
the lowering case. -/
theorem toggleOriginWalshIndex_eq_ite (i : Fin 2)
    (S : Finset LineIndex) :
    toggleOriginWalshIndex i S =
      if originLine i ∈ S then S.erase (originLine i)
      else insert (originLine i) S := by
  classical
  by_cases h : originLine i ∈ S
  · simp only [h, if_pos]
    ext l
    simp only [toggleOriginWalshIndex, Finset.mem_symmDiff,
      Finset.mem_singleton, Finset.mem_erase]
    by_cases hl : l = originLine i <;> simp_all
  · simp only [h]
    ext l
    simp only [toggleOriginWalshIndex, Finset.mem_symmDiff,
      Finset.mem_singleton]
    by_cases hl : l = originLine i <;> simp_all

@[simp] theorem translateWalshIndex_empty (x : Operator.Lattice) :
    translateWalshIndex x ∅ = ∅ := by
  simp [translateWalshIndex]

@[simp] theorem toggleOriginWalshIndex_empty (i : Fin 2) :
    toggleOriginWalshIndex i ∅ = {originLine i} := by
  ext l
  simp only [toggleOriginWalshIndex, Finset.mem_symmDiff,
    Finset.notMem_empty, Finset.mem_singleton]
  tauto

theorem environmentShift_walshL2_public (x : Operator.Lattice)
    (S : Finset LineIndex) :
    environmentShift x (walshL2 S) = walshL2 (translateWalshIndex x S) := by
  rw [environmentShift_walshL2]
  rfl

theorem originSignMultiplier_walshL2_public (i : Fin 2)
    (S : Finset LineIndex) :
    originSignMultiplier i (walshL2 S) = walshL2 (toggleOriginWalshIndex i S) := by
  rw [originSignMultiplier_walshL2]
  rfl

theorem originSignMultiplier_smul_walshL2 (i : Fin 2) (a : ℂ)
    (S : Finset LineIndex) :
    originSignMultiplier i (a • walshL2 S) =
      a • walshL2 (toggleOriginWalshIndex i S) := by
  rw [map_smul, originSignMultiplier_walshL2_public]

/-- The finite spatial coefficient of `S_p` applied to one Walsh monomial. -/
noncomputable def fiberSSpatialCoefficient (p : Fin 2 → ℝ)
    (S : Finset LineIndex) : WalshCoefficient :=
  (2 : ℂ)⁻¹ • ∑ i : Fin 2,
    (Finsupp.single (translateWalshIndex (Operator.axisVector i) S)
        (Complex.exp (Complex.I * p i)) +
      Finsupp.single (translateWalshIndex (-Operator.axisVector i) S)
        (Complex.exp (-Complex.I * p i)) -
      Finsupp.single S 2)

/-- The finite spatial coefficient of `A_p` applied to one Walsh monomial. -/
noncomputable def fiberASpatialCoefficient (p : Fin 2 → ℝ)
    (S : Finset LineIndex) : WalshCoefficient :=
  (2 : ℂ)⁻¹ • ∑ i : Fin 2,
    (Finsupp.single
        (toggleOriginWalshIndex i
          (translateWalshIndex (Operator.axisVector i) S))
        (Complex.exp (Complex.I * p i)) -
      Finsupp.single
        (toggleOriginWalshIndex i
          (translateWalshIndex (-Operator.axisVector i) S))
        (Complex.exp (-Complex.I * p i)))

/-- The degree-raising part of the concrete fiber operator on one Walsh
monomial, expressed using the Finset raising operator. -/
noncomputable def fiberDRaisingSpatialCoefficient (p : Fin 2 → ℝ)
    (S : Finset LineIndex) : WalshCoefficient :=
  (2 : ℂ)⁻¹ • ∑ i : Fin 2,
    (raiseCoefficient (originLine i)
        (Finsupp.single (translateWalshIndex (Operator.axisVector i) S)
          (Complex.exp (Complex.I * p i))) -
      raiseCoefficient (originLine i)
        (Finsupp.single (translateWalshIndex (-Operator.axisVector i) S)
          (Complex.exp (-Complex.I * p i))))

/-- The signed degree-lowering part `D⁺` on one Walsh monomial.  The minus
sign is the skew-adjoint convention, so `A = D - D⁺`. -/
noncomputable def fiberDStarLoweringSpatialCoefficient (p : Fin 2 → ℝ)
    (S : Finset LineIndex) : WalshCoefficient :=
  -((2 : ℂ)⁻¹ • ∑ i : Fin 2,
    (lowerCoefficient (originLine i)
        (Finsupp.single (translateWalshIndex (Operator.axisVector i) S)
          (Complex.exp (Complex.I * p i))) -
      lowerCoefficient (originLine i)
        (Finsupp.single (translateWalshIndex (-Operator.axisVector i) S)
          (Complex.exp (-Complex.I * p i)))))

/-- Coordinate toggling is exactly raising plus lowering on a singleton
coefficient. -/
theorem single_toggle_eq_raise_add_lower (i : Fin 2)
    (S : Finset LineIndex) (a : ℂ) :
    Finsupp.single (toggleOriginWalshIndex i S) a =
      raiseCoefficient (originLine i) (Finsupp.single S a) +
        lowerCoefficient (originLine i) (Finsupp.single S a) := by
  classical
  rw [toggleOriginWalshIndex_eq_ite]
  by_cases h : originLine i ∈ S <;> simp [h]

/-- Basis-level form of Lemma 5.1: the actual spatial coefficient of the
concrete skew fiber splits as `D - D⁺`. -/
theorem fiberASpatialCoefficient_eq_D_sub_DStar (p : Fin 2 → ℝ)
    (S : Finset LineIndex) :
    fiberASpatialCoefficient p S =
      fiberDRaisingSpatialCoefficient p S -
        fiberDStarLoweringSpatialCoefficient p S := by
  classical
  simp only [fiberASpatialCoefficient, fiberDRaisingSpatialCoefficient,
    fiberDStarLoweringSpatialCoefficient, sub_neg_eq_add]
  rw [← smul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [single_toggle_eq_raise_add_lower,
    single_toggle_eq_raise_add_lower]
  module

/-- The concrete `D` part maps degree `n` basis coefficients to degree
`n+1`. -/
theorem isWalshDegree_fiberDRaisingSpatialCoefficient {n : ℕ}
    (p : Fin 2 → ℝ) (S : Finset LineIndex) (hS : S.card = n) :
    IsWalshDegree (n + 1) (fiberDRaisingSpatialCoefficient p S) := by
  apply IsWalshDegree.smul
  apply isWalshDegree_sum Finset.univ
  intro i _
  apply IsWalshDegree.sub
  · apply isWalshDegree_raiseCoefficient_single
    exact (card_translateWalshIndex (Operator.axisVector i) S).trans hS
  · apply isWalshDegree_raiseCoefficient_single
    exact (card_translateWalshIndex (-Operator.axisVector i) S).trans hS

/-- The concrete signed `D⁺` part maps degree `n` basis coefficients to
degree `n-1`. -/
theorem isWalshDegree_fiberDStarLoweringSpatialCoefficient {n : ℕ}
    (p : Fin 2 → ℝ) (S : Finset LineIndex) (hS : S.card = n) :
    IsWalshDegree (n - 1) (fiberDStarLoweringSpatialCoefficient p S) := by
  apply IsWalshDegree.neg
  apply IsWalshDegree.smul
  apply isWalshDegree_sum Finset.univ
  intro i _
  apply IsWalshDegree.sub
  · apply isWalshDegree_lowerCoefficient_single
    exact (card_translateWalshIndex (Operator.axisVector i) S).trans hS
  · apply isWalshDegree_lowerCoefficient_single
    exact (card_translateWalshIndex (-Operator.axisVector i) S).trans hS

/-- Concrete `S_p` intertwining on every Walsh basis vector. -/
theorem concreteFiberS_walshL2 (p : Fin 2 → ℝ) (S : Finset LineIndex) :
    concreteFiberS p (walshL2 S) = walshSynthesis (fiberSSpatialCoefficient p S) := by
  rw [concreteFiberS_formula]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.id_apply,
    environmentShift_walshL2_public]
  rw [fiberSSpatialCoefficient, walshSynthesis_smul,
    walshSynthesis_sum Finset.univ]
  simp only [walshSynthesis_sub, walshSynthesis_add, walshSynthesis_single]

/-- In degree zero, `S_p` is the scalar `-θ(p)`, i.e. the degree-zero
case of (Hsym). -/
theorem concreteFiberS_empty (p : Fin 2 → ℝ) :
    concreteFiberS p (walshL2 ∅) =
      -(Operator.theta p : ℂ) • walshL2 ∅ := by
  rw [concreteFiberS_walshL2, fiberSSpatialCoefficient,
    Fin.sum_univ_two, walshSynthesis_smul]
  simp only [translateWalshIndex_empty, walshSynthesis_add,
    walshSynthesis_sub, walshSynthesis_single]
  rw [Operator.theta, Fin.sum_univ_two]
  unfold Operator.dispersion
  rw [show Complex.I * (p 0 : ℂ) = (p 0 : ℂ) * Complex.I by ring,
    show -Complex.I * (p 0 : ℂ) = (-(p 0 : ℂ)) * Complex.I by ring,
    show Complex.I * (p 1 : ℂ) = (p 1 : ℂ) * Complex.I by ring,
    show -Complex.I * (p 1 : ℂ) = (-(p 1 : ℂ)) * Complex.I by ring]
  simp only [Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  module

/-- Nonnegativity of the operator part's dispersion sum. -/
theorem operatorTheta_nonneg (p : Fin 2 → ℝ) :
    0 ≤ Operator.theta p := by
  unfold Operator.theta Operator.dispersion
  apply Finset.sum_nonneg
  intro i _
  linarith [Real.neg_one_le_cos (p i), Real.cos_le_one (p i)]

/-- The concrete degree-zero `H` multiplier is `λ+θ(p)`. -/
theorem concreteH_empty (lambda : ℝ) (p : Fin 2 → ℝ) :
    (concreteFiberEnvironment.dissipativeSkewPair p).H lambda (walshL2 ∅) =
      ((lambda + Operator.theta p : ℝ) : ℂ) • walshL2 ∅ := by
  rw [Operator.DissipativeSkewPair.H]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply]
  change (lambda : ℂ) • walshL2 ∅ - concreteFiberS p (walshL2 ∅) = _
  rw [concreteFiberS_empty]
  module

/-- The Lax--Milgram inverse of `H` is explicit on the constant Walsh
character. -/
theorem concreteHInverse_empty {lambda : ℝ} (hlambda : 0 < lambda)
    (p : Fin 2 → ℝ) :
    ((concreteFiberEnvironment.dissipativeSkewPair p).hEquiv hlambda).symm
        (walshL2 ∅) =
      (((lambda + Operator.theta p : ℝ)⁻¹ : ℝ) : ℂ) • walshL2 ∅ := by
  let P := concreteFiberEnvironment.dissipativeSkewPair p
  apply (P.H_bijective hlambda).1
  rw [P.H_apply_inverse]
  rw [map_smul, concreteH_empty]
  have hden : lambda + Operator.theta p ≠ 0 :=
    (add_pos_of_pos_of_nonneg hlambda (operatorTheta_nonneg p)).ne'
  rw [smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hden,
    Complex.ofReal_one, one_smul]

/-- The driftless dual energy is exactly the first entry of (13). -/
theorem concrete_hMinusEnergy_empty {lambda : ℝ} (hlambda : 0 < lambda)
    (p : Fin 2 → ℝ) :
    (concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy
        hlambda (walshL2 ∅) = Operator.driftlessMajorant lambda p := by
  rw [Operator.DissipativeSkewPair.hMinusEnergy]
  calc
    re ⟪walshL2 ∅,
        ((concreteFiberEnvironment.dissipativeSkewPair p).hEquiv hlambda).symm
          (walshL2 ∅)⟫_ℂ =
        re ⟪walshL2 ∅,
          (((lambda + Operator.theta p : ℝ)⁻¹ : ℝ) : ℂ) • walshL2 ∅⟫_ℂ := by
      exact congrArg (fun y : WalshL2 => re ⟪walshL2 ∅, y⟫_ℂ)
        (concreteHInverse_empty hlambda p)
    _ = (lambda + Operator.theta p)⁻¹ := by
      rw [inner_smul_right, inner_walshL2]
      change (((((lambda + Operator.theta p)⁻¹ : ℝ) : ℂ) * 1).re) =
        (lambda + Operator.theta p)⁻¹
      rw [mul_one]
      rfl
    _ = Operator.driftlessMajorant lambda p := by
      simp [Operator.driftlessMajorant, one_div]

/-- Concrete `A_p` intertwining on every Walsh basis vector. -/
theorem concreteFiberA_walshL2 (p : Fin 2 → ℝ) (S : Finset LineIndex) :
    concreteFiberA p (walshL2 S) = walshSynthesis (fiberASpatialCoefficient p S) := by
  rw [concreteFiberA_formula]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    environmentShift_walshL2_public]
  simp only [map_sub, originSignMultiplier_smul_walshL2]
  rw [fiberASpatialCoefficient, walshSynthesis_smul,
    walshSynthesis_sum Finset.univ]
  simp only [walshSynthesis_sub, walshSynthesis_single]

/-- The concrete fiber action itself is the synthesized `D - D⁺` split
on each Walsh basis vector. -/
theorem concreteFiberA_walshL2_eq_D_sub_DStar (p : Fin 2 → ℝ)
    (S : Finset LineIndex) :
    concreteFiberA p (walshL2 S) =
      walshSynthesis (fiberDRaisingSpatialCoefficient p S) -
        walshSynthesis (fiberDStarLoweringSpatialCoefficient p S) := by
  rw [concreteFiberA_walshL2,
    fiberASpatialCoefficient_eq_D_sub_DStar, walshSynthesis_sub]

/-- Translation parallel to a line fixes the line through the origin. -/
theorem translateWalshIndex_originLine_axis (i : Fin 2) (sign : ℤ) :
    translateWalshIndex (sign • Operator.axisVector i) {originLine i} =
      {originLine i} := by
  ext l
  fin_cases i <;>
    simp [translateWalshIndex, lineTranslation, latticeToSite,
      transverseCoordinate, Operator.axisVector, originLine, finAxis]

/-- The phase difference in `A_p` is `i sin(p_i)`. -/
theorem half_exp_I_sub_exp_neg_I (x : ℝ) :
    (2 : ℂ)⁻¹ *
        (Complex.exp (Complex.I * x) - Complex.exp (-Complex.I * x)) =
      Complex.I * (Real.sin x : ℂ) := by
  rw [show Complex.I * (x : ℂ) = (x : ℂ) * Complex.I by ring,
    Complex.exp_mul_I]
  rw [show -Complex.I * (x : ℂ) = (-(x : ℂ)) * Complex.I by ring,
    Complex.exp_mul_I]
  rw [Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin]
  ring

@[simp] theorem half_exp_I_sub_exp_neg_I_complex (x : ℝ) :
    (2 : ℂ)⁻¹ *
        (Complex.exp (Complex.I * x) - Complex.exp (-(Complex.I * x))) =
      Complex.I * Complex.sin (x : ℂ) := by
  simpa only [neg_mul, Complex.ofReal_sin] using half_exp_I_sub_exp_neg_I x

/-- The degree-zero coefficient of `A_p` on a one-line Walsh character.
This is the spatial version of the first formula in (D1). -/
theorem inner_empty_concreteFiberA_singleton (p : Fin 2 → ℝ)
    (i : Fin 2) (k : ℤ) :
    inner ℂ (walshL2 ∅) (concreteFiberA p (walshL2 {(finAxis i, k)})) =
      if k = 0 then Complex.I * (Real.sin (p i) : ℂ) else 0 := by
  classical
  rw [concreteFiberA_walshL2]
  conv_lhs =>
    lhs
    rw [show walshL2 ∅ = walshSynthesis (Finsupp.single ∅ 1) by simp]
  rw [inner_walshSynthesis]
  fin_cases i <;> by_cases hk : k = 0 <;>
    simp [walshCoefficientInner, fiberASpatialCoefficient,
      translateWalshIndex, toggleOriginWalshIndex, Operator.axisVector,
      originLine, latticeToSite, lineTranslation, transverseCoordinate,
      finAxis, hk]

/-- The action of the skew fiber on the constant character is the sum of
the two origin-line characters with their sine phases. -/
theorem concreteFiberA_empty (p : Fin 2 → ℝ) :
    concreteFiberA p (walshL2 ∅) =
      (Complex.I * (Real.sin (p 0) : ℂ)) •
          walshL2 {(Axis.horizontal, 0)} +
        (Complex.I * (Real.sin (p 1) : ℂ)) •
          walshL2 {(Axis.vertical, 0)} := by
  rw [concreteFiberA_walshL2, fiberASpatialCoefficient,
    Fin.sum_univ_two, walshSynthesis_smul]
  simp only [translateWalshIndex_empty, toggleOriginWalshIndex_empty,
    walshSynthesis_add, walshSynthesis_sub, walshSynthesis_single,
    originLine, finAxis]
  simp only [if_true, one_ne_zero, if_false]
  have h0 : (2 : ℂ)⁻¹ *
      (Complex.exp (Complex.I * (p 0 : ℂ)) -
        Complex.exp (-Complex.I * (p 0 : ℂ))) =
        Complex.I * (Real.sin (p 0) : ℂ) := by
    simpa only [neg_mul] using half_exp_I_sub_exp_neg_I (p 0)
  have h1 : (2 : ℂ)⁻¹ *
      (Complex.exp (Complex.I * (p 1 : ℂ)) -
        Complex.exp (-Complex.I * (p 1 : ℂ))) =
        Complex.I * (Real.sin (p 1) : ℂ) := by
    simpa only [neg_mul] using half_exp_I_sub_exp_neg_I (p 1)
  calc
    _ = ((2 : ℂ)⁻¹ *
          (Complex.exp (Complex.I * (p 0 : ℂ)) -
            Complex.exp (-Complex.I * (p 0 : ℂ)))) •
            walshL2 {(Axis.horizontal, 0)} +
        ((2 : ℂ)⁻¹ *
          (Complex.exp (Complex.I * (p 1 : ℂ)) -
            Complex.exp (-Complex.I * (p 1 : ℂ)))) •
            walshL2 {(Axis.vertical, 0)} := by module
    _ = _ := by rw [h0, h1]

/-- Complete degree-one form of the first identity in (D1): the constant
coefficient of `A_p f` is the zero Fourier coefficient times
`i sin(p₁)`. -/
theorem inner_empty_concreteFiberA_axisDegreeOne (p : Fin 2 → ℝ)
    (c : RowLineCoefficient) :
    inner ℂ (walshL2 ∅)
      (concreteFiberA p (axisDegreeOneSynthesis Axis.horizontal c)) =
        Complex.I * (Real.sin (p 0) : ℂ) * c 0 := by
  rw [← (concreteFiberA p).adjoint_inner_left]
  rw [concreteFiberA_skewAdjoint, ContinuousLinearMap.neg_apply,
    concreteFiberA_empty]
  rw [inner_neg_left, inner_add_left, inner_smul_left, inner_smul_left,
    inner_axisDegreeOneSynthesis,
    inner_axisDegreeOneSynthesis_of_ne Axis.horizontal Axis.vertical
      (by decide)]
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, mul_zero,
    add_zero]
  ring

/-- Frequency-space version of the same constant-component identity. -/
theorem inner_empty_concreteFiberA_degreeOneRealFrequency
    (p : Fin 2 → ℝ) (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Set.Ioc (-Real.pi) Real.pi))) :
    inner ℂ (walshL2 ∅)
      (concreteFiberA p
        (degreeOneRealFrequencySynthesis Axis.horizontal f hf)) =
      Complex.I * (Real.sin (p 0) : ℂ) *
        ((2 * Real.pi)⁻¹ * ∫ r in Set.Ioc (-Real.pi) Real.pi, f r) := by
  rw [degreeOneRealFrequencySynthesis, degreeOneFrequencySynthesis]
  change inner ℂ (walshL2 ∅)
    (concreteFiberA p
      (axisDegreeOneSynthesis Axis.horizontal
        (fourierBasis.repr (realTorusL2 f hf)))) = _
  rw [inner_empty_concreteFiberA_axisDegreeOne]
  rw [fourierBasis_repr_realTorusL2_zero]

/-- A type-`(1,1,2)` correction has no degree-zero component after applying
the skew fiber. -/
theorem inner_empty_concreteFiberA_type112 (p : Fin 2 → ℝ)
    (c : ℓ²(Type112Index, ℂ)) :
    inner ℂ (walshL2 ∅)
      (concreteFiberA p (type112WalshSynthesis c)) = 0 := by
  rw [← (concreteFiberA p).adjoint_inner_left]
  rw [concreteFiberA_skewAdjoint, ContinuousLinearMap.neg_apply,
    concreteFiberA_empty, inner_neg_left, inner_add_left,
    inner_smul_left, inner_smul_left,
    inner_type112WalshSynthesis_eq_zero,
    inner_type112WalshSynthesis_eq_zero]
  · simp
  · simp
  · simp

/-- At zero external frequency the constant Walsh character is killed by
the concrete skew fiber. -/
@[simp] theorem concreteFiberA_zero_empty :
    concreteFiberA (0 : Fin 2 → ℝ) (walshL2 ∅) = 0 := by
  rw [concreteFiberA_walshL2, fiberASpatialCoefficient]
  simp [translateWalshIndex_empty, toggleOriginWalshIndex_empty]
  exact map_zero (Finsupp.linearCombination ℂ walshL2)

/-- Skew-adjointness transfers the preceding identity to the constant
coefficient of `A₀ g`, for every Walsh-space vector `g`. -/
theorem inner_empty_concreteFiberA_zero (g : WalshL2) :
    inner ℂ (walshL2 ∅) (concreteFiberA (0 : Fin 2 → ℝ) g) = 0 := by
  rw [← (concreteFiberA (0 : Fin 2 → ℝ)).adjoint_inner_left]
  rw [concreteFiberA_skewAdjoint]
  simp

/-- Consequently exact constant cancellation is impossible at `p=0`.
This is why the corrected certificate must use the paper's separate `g=0`
low-frequency branch. -/
theorem inner_empty_residual_zero_frequency (g : WalshL2) :
    inner ℂ (walshL2 ∅)
      (walshL2 ∅ - concreteFiberA (0 : Fin 2 → ℝ) g) = 1 := by
  rw [inner_sub_right, inner_walshL2, inner_empty_concreteFiberA_zero]
  simp

end

end Manhattan
