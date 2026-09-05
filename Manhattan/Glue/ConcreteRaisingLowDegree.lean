import Manhattan.Glue.ConcreteRaisingFourier

/-!
# The low-degree instances of Lemma 5.1

The identities (D1), (D2a) and (D2b) of `manuscript.tex:793-822` are the
degree `0 -> 1` and `1 -> 2` cases of equation (45). They are derived here from
the general formulas of `Manhattan/Glue/ConcreteRaising.lean`, for the actual
operator `concreteFiberA`.

In the Finset convention the manuscript's normalizing factors
`sqrt 2` and `2` on the coefficients of types `11` and `12` do not appear: the
Finset synthesis maps are literal isometries, and the symmetrization which
produces `f(r) + f(r')` in (D2a) is replaced by the single term whose omitted
line is the origin line.

Paper: `manuscript.tex:793-822`, `manuscript.tex:1199-1205`.
-/

open ComplexConjugate InnerProductSpace MeasureTheory
open scoped BigOperators ComplexConjugate InnerProduct

namespace Manhattan.Glue

noncomputable section

/-! ### Translating a single line -/

theorem translateWalshIndex_singleton_axis (i : Fin 2) (sign : ℤ) (a : Axis)
    (k : ℤ) :
    translateWalshIndex (sign • Operator.axisVector i) {(a, k)} =
      {(a, k + sign * axisShift i a)} := by
  rw [translateWalshIndex, Finset.map_singleton]
  simp only [Equiv.coe_toEmbedding, lineTranslation, Equiv.coe_fn_mk]
  rw [transverseCoordinate_latticeToSite_smul_axisVector]

theorem translateWalshIndex_singleton_pos (i : Fin 2) (a : Axis) (k : ℤ) :
    translateWalshIndex (Operator.axisVector i) {(a, k)} =
      {(a, k + axisShift i a)} := by
  simpa using translateWalshIndex_singleton_axis i 1 a k

theorem translateWalshIndex_singleton_neg (i : Fin 2) (a : Axis) (k : ℤ) :
    translateWalshIndex (-Operator.axisVector i) {(a, k)} =
      {(a, k - axisShift i a)} := by
  have h := translateWalshIndex_singleton_axis i (-1) a k
  simp only [neg_smul, one_smul] at h
  rw [h]
  congr 2
  ring

/-! ### Degree zero to one: identity (D1) -/

/-- The constant character is annihilated by `D*`. -/
@[simp] theorem walshLower_walshL2_empty (p : Fin 2 → ℝ) :
    walshLower p (walshL2 ∅) = 0 := by
  rw [walshLower, ContinuousLinearMap.sum_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [walshLowerDir, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    fiberSkewTerm_walshL2]
  simp only [translateWalshIndex_empty, map_sub, map_smul, originLower_walshL2,
    Finset.notMem_empty, if_false, smul_zero, sub_self, neg_zero]

/-- **(D1), raising half.** The degree-zero to degree-one action of the actual
skew fiber is `i sin(p_i)` on each of the two origin lines. -/
theorem walshRaise_walshL2_empty (p : Fin 2 → ℝ) :
    walshRaise p (walshL2 ∅) =
      (Complex.I * (Real.sin (p 0) : ℂ)) • walshL2 {(Axis.horizontal, 0)} +
        (Complex.I * (Real.sin (p 1) : ℂ)) • walshL2 {(Axis.vertical, 0)} := by
  have h : walshRaise p (walshL2 ∅) - walshLower p (walshL2 ∅) =
      (Complex.I * (Real.sin (p 0) : ℂ)) • walshL2 {(Axis.horizontal, 0)} +
        (Complex.I * (Real.sin (p 1) : ℂ)) • walshL2 {(Axis.vertical, 0)} := by
    rw [← ContinuousLinearMap.sub_apply,
      ← concreteFiberA_eq_walshRaise_sub_walshLower]
    exact concreteFiberA_empty p
  rwa [walshLower_walshL2_empty, sub_zero] at h

/-- Raising never produces a degree-zero component. -/
@[simp] theorem inner_empty_walshRaise (p : Fin 2 → ℝ) (x : WalshL2) :
    inner ℂ (walshL2 ∅) (walshRaise p x) = 0 := by
  rw [inner_walshL2_walshRaise]
  exact Finset.sum_eq_zero fun i _ => if_neg (by simp)

/-- Consequently the degree-zero component of `A x` is carried entirely by
`D*`. -/
theorem inner_empty_walshLower (p : Fin 2 → ℝ) (x : WalshL2) :
    inner ℂ (walshL2 ∅) (walshLower p x) =
      -inner ℂ (walshL2 ∅) (concreteFiberA p x) := by
  rw [concreteFiberA_eq_walshRaise_sub_walshLower,
    ContinuousLinearMap.sub_apply, inner_sub_right, inner_empty_walshRaise]
  ring

/-- **(D1), lowering half.** `D_0^* f = -i sin(p_1) * (zero frequency of f)`,
in the manuscript's indexing where the row axis is the first coordinate. -/
theorem inner_empty_walshLower_axisDegreeOne (p : Fin 2 → ℝ)
    (c : RowLineCoefficient) :
    inner ℂ (walshL2 ∅)
        (walshLower p (axisDegreeOneSynthesis Axis.horizontal c)) =
      -(Complex.I * (Real.sin (p 0) : ℂ) * c 0) := by
  rw [inner_empty_walshLower, inner_empty_concreteFiberA_axisDegreeOne]

/-! ### Degree one to two: identities (D2a) and (D2b) -/

private theorem originLine_zero : originLine 0 = (Axis.horizontal, 0) := rfl

private theorem axisShift_zero_horizontal : axisShift 0 Axis.horizontal = 0 := by
  simp [axisShift]

private theorem axisShift_one_horizontal : axisShift 1 Axis.horizontal = 1 := by
  simp [axisShift, finAxis]

private theorem originLine_one : originLine 1 = (Axis.vertical, 0) := rfl

/-- **(D2a), raising half.** Appending the origin *row* to a row coefficient
multiplies it by `i sin(p_1)` in the manuscript's indexing; the total frequency
of the two-row output has first coordinate `p_1`, because rows carry no
frequency in that direction. -/
theorem inner_twoRow_walshRaise_axisDegreeOne (p : Fin 2 → ℝ)
    (c : RowLineCoefficient) (y : ℤ) (hy : y ≠ 0) :
    inner ℂ (walshL2 {(Axis.horizontal, 0), (Axis.horizontal, y)})
        (walshRaise p (axisDegreeOneSynthesis Axis.horizontal c)) =
      Complex.I * (Real.sin (p 0) : ℂ) * c y := by
  have hmem : originLine 0 ∉ ({(Axis.horizontal, y)} : Finset LineIndex) := by
    simp only [originLine_zero, Finset.mem_singleton, Prod.mk.injEq, not_and]
    exact fun _ => Ne.symm hy
  have hother : originLine 1 ∉
      insert (originLine 0) ({(Axis.horizontal, y)} : Finset LineIndex) := by
    simp [originLine_zero, originLine_one]
  have hT : ({(Axis.horizontal, 0), (Axis.horizontal, y)} : Finset LineIndex) =
      insert (originLine 0) {(Axis.horizontal, y)} := rfl
  rw [hT, inner_walshL2_walshRaise, Fin.sum_univ_two,
    if_pos (Finset.mem_insert_self _ _), if_neg hother, add_zero,
    Finset.erase_insert hmem, translateWalshIndex_singleton_pos,
    translateWalshIndex_singleton_neg]
  rw [axisShift_zero_horizontal, add_zero, sub_zero,
    inner_axisDegreeOneSynthesis]
  have hsin := half_exp_I_sub_exp_neg_I (p 0)
  linear_combination (c y) * hsin

/-- **(D2b), raising half.** Appending the origin *column* to a row
coefficient gives the phase difference whose symbol is `i sin(r)`, where `r` is
the shifted row frequency; see `raisingSymbol_apply`. -/
theorem inner_mixed_walshRaiseDir_axisDegreeOne (p : Fin 2 → ℝ)
    (c : RowLineCoefficient) (y : ℤ) :
    inner ℂ (walshL2 {(Axis.vertical, 0), (Axis.horizontal, y)})
        (walshRaiseDir p 1 (axisDegreeOneSynthesis Axis.horizontal c)) =
      (2 : ℂ)⁻¹ *
        (Complex.exp (Complex.I * p 1) * c (y - 1) -
          Complex.exp (-Complex.I * p 1) * c (y + 1)) := by
  have hmem : originLine 1 ∉ ({(Axis.horizontal, y)} : Finset LineIndex) := by
    simp [originLine_one]
  have hT : ({(Axis.vertical, 0), (Axis.horizontal, y)} : Finset LineIndex) =
      insert (originLine 1) {(Axis.horizontal, y)} := rfl
  rw [hT, inner_walshL2_walshRaiseDir, if_pos (Finset.mem_insert_self _ _),
    Finset.erase_insert hmem, translateWalshIndex_singleton_pos,
    translateWalshIndex_singleton_neg]
  rw [axisShift_one_horizontal, inner_axisDegreeOneSynthesis,
    inner_axisDegreeOneSynthesis]

/-- The same, for the full raising operator, off the coincidence `y = 0`. -/
theorem inner_mixed_walshRaise_axisDegreeOne (p : Fin 2 → ℝ)
    (c : RowLineCoefficient) (y : ℤ) (hy : y ≠ 0) :
    inner ℂ (walshL2 {(Axis.vertical, 0), (Axis.horizontal, y)})
        (walshRaise p (axisDegreeOneSynthesis Axis.horizontal c)) =
      (2 : ℂ)⁻¹ *
        (Complex.exp (Complex.I * p 1) * c (y - 1) -
          Complex.exp (-Complex.I * p 1) * c (y + 1)) := by
  have hother : originLine 0 ∉
      insert (originLine 1) ({(Axis.horizontal, y)} : Finset LineIndex) := by
    simp only [originLine_zero, originLine_one, Finset.mem_insert,
      Finset.mem_singleton, Prod.mk.injEq, not_or, not_and]
    exact ⟨by simp, fun _ => Ne.symm hy⟩
  have hT : ({(Axis.vertical, 0), (Axis.horizontal, y)} : Finset LineIndex) =
      insert (originLine 1) {(Axis.horizontal, y)} := rfl
  rw [hT, walshRaise, ContinuousLinearMap.sum_apply, inner_sum, Fin.sum_univ_two]
  rw [inner_walshL2_walshRaiseDir, if_neg hother, zero_add, ← hT]
  exact inner_mixed_walshRaiseDir_axisDegreeOne p c y

/-! ### The degree one to two symbol

Instantiating the general symbol of `raisingSymbol` at the one-line row pattern
turns (D2a) and (D2b) into the manuscript's `i sin(p_1)` and `i sin(r)`, where
`r` is the shifted row frequency of `manuscript.tex:768-771`. -/

attribute [local instance] Real.fact_zero_lt_one
attribute [local instance] concreteRaisingUnitAddCircleMeasureSpace
attribute [local instance] concreteRaisingUnitAddCircleIsProbabilityMeasure

open UnitAddTorus

theorem patternLines_unit_horizontal (n : Unit → ℤ) :
    patternLines (fun _ : Unit => Axis.horizontal) n =
      {(Axis.horizontal, n ())} := by
  ext l
  simp [patternLines]

/-- The symbol of (D2a): appending a row leaves the first coordinate of the
total frequency equal to `p_1`. -/
theorem raisingSymbol_row_horizontal (p : Fin 2 → ℝ) (θ : ℝ) :
    raisingSymbol p 0 (fun _ : Unit => Axis.horizontal)
        (fun _ : Unit => ((θ : ℝ) : UnitAddCircle)) =
      Complex.I * (Real.sin (p 0) : ℂ) := by
  rw [raisingSymbol_apply p 0 (fun _ : Unit => Axis.horizontal) fun _ => θ]
  simp [axisShift_zero_horizontal]

/-- The symbol of (D2b): appending a column makes the second coordinate of the
total frequency equal to `r = p_2 + s`, where `s = 2 pi θ` is the row
frequency. -/
theorem raisingSymbol_column_horizontal (p : Fin 2 → ℝ) (θ : ℝ) :
    raisingSymbol p 1 (fun _ : Unit => Axis.horizontal)
        (fun _ : Unit => ((θ : ℝ) : UnitAddCircle)) =
      Complex.I * (Real.sin (p 1 + 2 * Real.pi * θ) : ℂ) := by
  rw [raisingSymbol_apply p 1 (fun _ : Unit => Axis.horizontal) fun _ => θ]
  simp [axisShift_one_horizontal]

/-- **(D2b) in frequency form.** If the row coefficient of `x` is the Fourier
coefficient sequence of `F`, then the mixed coefficient of `D x` is the Fourier
coefficient sequence of `i sin(r) F`. -/
theorem inner_mixed_walshRaiseDir_mFourierCoeff (p : Fin 2 → ℝ) (x : WalshL2)
    (F : UnitAddTorus Unit → ℂ) (hF : Integrable F volume)
    (hFx : ∀ m : Unit → ℤ,
      inner ℂ (walshL2 {(Axis.horizontal, m ())}) x = mFourierCoeff F m)
    (n : Unit → ℤ) :
    inner ℂ (walshL2 {(Axis.vertical, 0), (Axis.horizontal, n ())})
        (walshRaiseDir p 1 x) =
      mFourierCoeff
        (fun t => raisingSymbol p 1 (fun _ : Unit => Axis.horizontal) t * F t) n := by
  have hn : originLine 1 ∉ patternLines (fun _ : Unit => Axis.horizontal) n := by
    rw [patternLines_unit_horizontal]
    simp [originLine_one]
  have hFx' : ∀ m : Unit → ℤ,
      inner ℂ (walshL2 (patternLines (fun _ : Unit => Axis.horizontal) m)) x =
        mFourierCoeff F m := by
    intro m
    rw [patternLines_unit_horizontal]
    exact hFx m
  have h := inner_walshL2_walshRaiseDir_mFourierCoeff
    (fun _ : Unit => Axis.horizontal) p 1 x F hF hFx' n hn
  rwa [patternLines_unit_horizontal,
    show insert (originLine 1) ({(Axis.horizontal, n ())} : Finset LineIndex) =
      {(Axis.vertical, 0), (Axis.horizontal, n ())} from rfl] at h

end

end Manhattan.Glue
