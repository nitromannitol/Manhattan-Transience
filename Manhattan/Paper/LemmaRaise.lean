import Manhattan.Glue.RaisingEnergy

/-!
# Lemma 5.1 at every degree

`lem:raise` (`manuscript.tex:1179-1191`) describes the raising operator in the
symmetric coefficients of Section 3.1: a degree-`n` element is
`F = ∑_t f(t) ∏_a ω(t_a)` over ordered `n`-tuples `t` of line indices, with `f`
symmetric and vanishing when two line indices coincide.  The raising operator
computed without imposing distinct line indices, `D̃_n`, shifts, appends the
origin line of the direction of the shift, and distributes the new index among
the `n + 1` slots.  The lemma states

* `eq:raise`: `(D̃_n f)_{j₁…j_{n+1}} = (i/(n+1)) ∑_a sin(P_{j_a}) f_{j₁…ĵ_a…j_{n+1}}`;
* `D_n = Π_{n+1} D̃_n Π_n`, where `Π_n` projects onto coefficients supported on
  distinct line indices;
* `Π_n` commutes with every continuous multiplier that is a function of `P`.

This file proves the first two clauses for every `n`.

* `symCoeff n F` is the symmetric coefficient of a Walsh vector `F`:
  `(n!)⁻¹ ⟨W_S, F⟩` at every ordering of a set `S` of `n` distinct lines, and
  `0` at tuples with a repeated line (`symCoeff_apply`).
* `rawRaise n p` is `D̃_n` on ordered coefficients; the paper's `Π_n` is
  `Manhattan.Glue.offDiagonalProjection n`.
* `symCoeff_walshRaise` is `D_n = Π_{n+1} D̃_n Π_n`: the symmetric coefficient
  of `D F` is `Π_{n+1} D̃_n Π_n` applied to the symmetric coefficient of `F`.
  Here `D` is the raising part of `A_p = D - D*` (`Manhattan.Glue.walshRaise`).
* `orderedFourier_rawRaise` is `eq:raise` on the line-frequency side of
  equation (20): `P` is `Manhattan.Glue.totalFrequency`, the slot `a` of axis
  `j_a` carries `sin(P_{j_a})`, and the `a`-th term reads the coefficient after
  deleting the `a`-th line index and its frequency.
-/

open MeasureTheory UnitAddTorus
open Manhattan Manhattan.Glue

namespace Manhattan.Paper

noncomputable section

attribute [local instance] Manhattan.Glue.lineOrder

/-! ### Symmetric coefficients -/

/-- Permutation of the slots of an ordered coefficient. -/
def slotPermute (n : ℕ) (π : Equiv.Perm (Fin n)) :
    OrderedCoefficient n ≃ₗᵢ[ℂ] OrderedCoefficient n :=
  l2CongrLeft (Equiv.arrowCongr π (Equiv.refl LineIndex))

theorem slotPermute_apply (n : ℕ) (π : Equiv.Perm (Fin n)) (c : OrderedCoefficient n)
    (t : Fin n → LineIndex) : slotPermute n π c t = c (t ∘ π) := rfl

/-- The symmetric degree-`n` coefficient of a Walsh vector `F`, in the
normalization of Section 3.1 of the paper: the coefficient `f` with
`F = ∑_t f(t) ∏_a ω(t_a)` on the degree-`n` component of `F`. -/
def symCoeff (n : ℕ) (F : WalshL2) : OrderedCoefficient n :=
  ((n.factorial : ℂ)⁻¹) • ∑ π : Equiv.Perm (Fin n),
    slotPermute n π (walshOrdered n (walshSectorAnalysis (fun S => S.card = n) F))

theorem injective_degreeEnum_apply {n : ℕ} (S : WalshDegreeIndex n) :
    Function.Injective (degreeEnum S) :=
  (S.1.orderEmbOfFin S.2).injective

theorem sum_walshOrdered_comp_perm {n : ℕ} (d : DegreeCoefficient n)
    (t : Fin n → LineIndex) :
    (∑ π : Equiv.Perm (Fin n), walshOrdered n d (t ∘ π)) =
      if ht : Function.Injective t then
        d ⟨Finset.univ.image t, by rw [Finset.card_image_of_injective _ ht, Finset.card_fin]⟩
      else 0 := by
  classical
  by_cases ht : Function.Injective t
  · rw [dif_pos ht]
    set S : WalshDegreeIndex n :=
      ⟨Finset.univ.image t, by rw [Finset.card_image_of_injective _ ht, Finset.card_fin]⟩
      with hS
    set π₀ : Equiv.Perm (Fin n) := Tuple.sort t
    have hπ₀ : t ∘ π₀ = degreeEnum S := by
      refine Finset.orderEmbOfFin_unique S.2 (fun a => ?_) ?_
      · exact Finset.mem_image_of_mem t (Finset.mem_univ _)
      · exact (Tuple.monotone_sort t).strictMono_of_injective (ht.comp π₀.injective)
    rw [Finset.sum_eq_single π₀]
    · rw [hπ₀, walshOrdered_apply_degreeEnum]
    · intro π _ hπ
      refine walshOrdered_apply_of_notMem_degreeRange n d ?_
      rintro ⟨S', hS'⟩
      have hset : S' = S := by
        apply Subtype.ext
        apply Finset.coe_injective
        rw [← range_degreeEnum, hS', Set.range_comp, Equiv.range_eq_univ, Set.image_univ]
        simp [hS]
      apply hπ
      have h1 : t ∘ π = t ∘ π₀ := by rw [← hS', hset, hπ₀]
      exact Equiv.ext fun a => ht (congrFun h1 a)
    · intro h
      exact absurd (Finset.mem_univ π₀) h
  · rw [dif_neg ht]
    refine Finset.sum_eq_zero fun π _ => walshOrdered_apply_of_notMem_degreeRange n d ?_
    rintro ⟨S', hS'⟩
    apply ht
    have hinj : Function.Injective (t ∘ π) := by
      rw [← hS']
      exact injective_degreeEnum_apply S'
    intro a b hab
    have := @hinj (π.symm a) (π.symm b) (by simpa using hab)
    simpa using this

theorem symCoeff_apply (n : ℕ) (F : WalshL2) (t : Fin n → LineIndex) :
    symCoeff n F t =
      if Function.Injective t then
        (n.factorial : ℂ)⁻¹ * inner ℂ (walshL2 (Finset.univ.image t)) F
      else 0 := by
  have hsum : symCoeff n F t = (n.factorial : ℂ)⁻¹ * ∑ π : Equiv.Perm (Fin n),
      walshOrdered n (walshSectorAnalysis (fun S => S.card = n) F) (t ∘ π) := by
    rw [← l2Eval_apply t, symCoeff, map_smul, map_sum, smul_eq_mul]
    rfl
  rw [hsum, sum_walshOrdered_comp_perm]
  by_cases ht : Function.Injective t
  · rw [dif_pos ht, if_pos ht, walshSectorAnalysis_apply]
  · rw [dif_neg ht, if_neg ht, mul_zero]

/-- The symmetric coefficient is supported on distinct line indices. -/
theorem offDiagonalProjection_symCoeff (n : ℕ) (F : WalshL2) :
    offDiagonalProjection n (symCoeff n F) = symCoeff n F := by
  apply lp.ext
  funext t
  rw [offDiagonalProjection_apply, symCoeff_apply]
  by_cases ht : Function.Injective t <;> simp [ht]

/-! ### The raw raising operator `D̃_n` -/

/-- The shift of the direction-`i` raising on ordered coefficients,
`½(e^{i p_i} τ_{e_i} - e^{-i p_i} τ_{-e_i})`. -/
def orderedRaiseShift (n : ℕ) (p : Fin 2 → ℝ) (i : Fin 2) :
    OrderedCoefficient n →L[ℂ] OrderedCoefficient n :=
  (2 : ℂ)⁻¹ • (Complex.exp (Complex.I * p i) •
      (orderedTranslate n (Operator.axisVector i)).toLinearIsometry.toContinuousLinearMap -
    Complex.exp (-Complex.I * p i) •
      (orderedTranslate n (-Operator.axisVector i)).toLinearIsometry.toContinuousLinearMap)

/-- **The raising operator computed without imposing distinct line indices**,
`D̃_n`: in each direction `i`, shift, append the origin line of axis `i`, and
average the position of the new index over the `n + 1` slots. -/
def rawRaise (n : ℕ) (p : Fin 2 → ℝ) :
    OrderedCoefficient n →L[ℂ] OrderedCoefficient (n + 1) :=
  (((n + 1 : ℕ) : ℂ)⁻¹) • ∑ i : Fin 2, ∑ r : Fin (n + 1),
    insertLine n r i ∘L orderedRaiseShift n p i

theorem tupleTranslate_symm_apply (n : ℕ) (x : Operator.Lattice) (t : Fin n → LineIndex) :
    (tupleTranslate n x).symm t = tupleTranslate n (-x) t := by
  funext a
  rw [tupleTranslate_apply, latticeToSite_neg]
  apply (lineTranslation (latticeToSite x)).injective
  rw [show (tupleTranslate n x).symm t a = (lineTranslation (latticeToSite x)).symm (t a)
    from rfl, Equiv.apply_symm_apply]
  have h := lineTranslation_neg_cancel (latticeToSite x)
    ((lineTranslation (-latticeToSite x)) (t a))
  have h2 := lineTranslation_neg_cancel (-latticeToSite x) (t a)
  rw [neg_neg] at h2
  rw [h2]

theorem orderedTranslate_apply (n : ℕ) (x : Operator.Lattice) (c : OrderedCoefficient n)
    (t : Fin n → LineIndex) :
    orderedTranslate n x c t = c (tupleTranslate n (-x) t) := by
  rw [← tupleTranslate_symm_apply]
  rfl

theorem orderedRaiseShift_apply (n : ℕ) (p : Fin 2 → ℝ) (i : Fin 2)
    (c : OrderedCoefficient n) (t : Fin n → LineIndex) :
    orderedRaiseShift n p i c t =
      (2 : ℂ)⁻¹ * (Complex.exp (Complex.I * p i) *
          c (tupleTranslate n (-Operator.axisVector i) t) -
        Complex.exp (-Complex.I * p i) * c (tupleTranslate n (Operator.axisVector i) t)) := by
  rw [← l2Eval_apply t, orderedRaiseShift]
  simp only [smul_apply, sub_apply, map_smul, map_sub,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
    l2Eval_apply, orderedTranslate_apply, neg_neg, smul_eq_mul]

theorem insertLine_apply (n : ℕ) (r : Fin (n + 1)) (i : Fin 2) (c : OrderedCoefficient n)
    (u : Fin (n + 1) → LineIndex) :
    insertLine n r i c u = if u r = originLine i then c (Fin.removeNth r u) else 0 := by
  by_cases hu : u r = originLine i
  · rw [if_pos hu]
    have hu' : u = insertLineIndex n r i (Fin.removeNth r u) := by
      rw [insertLineIndex, ← hu, Fin.insertNth_self_removeNth]
    conv_lhs => rw [hu']
    rw [insertLine_apply_image]
  · rw [if_neg hu, insertLine_apply_of_notMem n r i c u hu]

theorem rawRaise_apply (n : ℕ) (p : Fin 2 → ℝ) (c : OrderedCoefficient n)
    (u : Fin (n + 1) → LineIndex) :
    rawRaise n p c u = ((n + 1 : ℕ) : ℂ)⁻¹ * ∑ i : Fin 2, ∑ r : Fin (n + 1),
      if u r = originLine i then orderedRaiseShift n p i c (Fin.removeNth r u) else 0 := by
  rw [← l2Eval_apply u, rawRaise]
  simp only [smul_apply, sum_apply, map_smul, map_sum,
    ContinuousLinearMap.comp_apply, l2Eval_apply, insertLine_apply, smul_eq_mul]

/-! ### `D_n = Π_{n+1} D̃_n Π_n` -/

theorem image_removeNth {n : ℕ} {u : Fin (n + 1) → LineIndex} (hu : Function.Injective u)
    (r : Fin (n + 1)) :
    Finset.univ.image (Fin.removeNth r u) = (Finset.univ.image u).erase (u r) := by
  classical
  ext l
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_erase, Fin.removeNth_apply]
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨fun h => Fin.succAbove_ne r j (hu h), ⟨_, rfl⟩⟩
  · rintro ⟨hne, k, rfl⟩
    have hk : k ≠ r := fun h => hne (by rw [h])
    obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hk
    exact ⟨j, rfl⟩

theorem injective_removeNth {n : ℕ} {u : Fin (n + 1) → LineIndex}
    (hu : Function.Injective u) (r : Fin (n + 1)) :
    Function.Injective (Fin.removeNth r u) :=
  hu.comp (Fin.succAbove_right_injective (p := r))

theorem injective_tupleTranslate_iff (n : ℕ) (x : Operator.Lattice) (t : Fin n → LineIndex) :
    Function.Injective (tupleTranslate n x t) ↔ Function.Injective t :=
  injective_tupleTranslate n x t

theorem image_tupleTranslate (n : ℕ) (x : Operator.Lattice) (t : Fin n → LineIndex) :
    Finset.univ.image (tupleTranslate n x t) =
      translateWalshIndex x (Finset.univ.image t) := by
  classical
  rw [translateWalshIndex, Finset.map_eq_image, Finset.image_image]
  rfl

/-- At an injective tuple the slot sum of the appended origin line has at most
one nonzero term, the slot carrying the origin line. -/
theorem sum_ite_originLine {n : ℕ} {u : Fin (n + 1) → LineIndex}
    (hu : Function.Injective u) (i : Fin 2) (g : (Fin n → LineIndex) → ℂ) :
    (∑ r : Fin (n + 1), if u r = originLine i then g (Fin.removeNth r u) else 0) =
      if h : originLine i ∈ Finset.univ.image u then
        g (Fin.removeNth (Classical.choose (Finset.mem_image.mp h)) u)
      else 0 := by
  classical
  by_cases h : originLine i ∈ Finset.univ.image u
  · rw [dif_pos h]
    set r₀ := Classical.choose (Finset.mem_image.mp h)
    have hr₀ : u r₀ = originLine i := (Classical.choose_spec (Finset.mem_image.mp h)).2
    rw [Finset.sum_eq_single r₀]
    · rw [if_pos hr₀]
    · intro r _ hr
      rw [if_neg]
      intro hc
      exact hr (hu (hc.trans hr₀.symm))
    · intro hc
      exact absurd (Finset.mem_univ r₀) hc
  · rw [dif_neg h]
    refine Finset.sum_eq_zero fun r _ => ?_
    rw [if_neg]
    intro hc
    exact h (Finset.mem_image.mpr ⟨r, Finset.mem_univ _, hc⟩)

/-- **`D_n = Π_{n+1} D̃_n Π_n`** (`lem:raise`).  The symmetric coefficient of
`D F` is `Π_{n+1} D̃_n Π_n` applied to the symmetric coefficient of `F`. -/
theorem symCoeff_walshRaise (n : ℕ) (p : Fin 2 → ℝ) (F : WalshL2) :
    symCoeff (n + 1) (walshRaise p F) =
      offDiagonalProjection (n + 1)
        (rawRaise n p (offDiagonalProjection n (symCoeff n F))) := by
  classical
  apply lp.ext
  funext u
  rw [offDiagonalProjection_apply, symCoeff_apply, offDiagonalProjection_symCoeff]
  by_cases hu : Function.Injective u
  · rw [if_pos hu, if_pos hu, rawRaise_apply, walshRaise, sum_apply, inner_sum,
      Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_walshL2_walshRaiseDir, sum_ite_originLine hu i]
    by_cases hi : originLine i ∈ Finset.univ.image u
    · rw [if_pos hi, dif_pos hi]
      set r₀ := Classical.choose (Finset.mem_image.mp hi)
      have hr₀ : u r₀ = originLine i := (Classical.choose_spec (Finset.mem_image.mp hi)).2
      have hv := injective_removeNth hu r₀
      have himage := image_removeNth hu r₀
      rw [hr₀] at himage
      rw [orderedRaiseShift_apply, symCoeff_apply, symCoeff_apply,
        if_pos ((injective_tupleTranslate_iff n _ _).mpr hv),
        if_pos ((injective_tupleTranslate_iff n _ _).mpr hv),
        image_tupleTranslate, image_tupleTranslate, himage, Nat.factorial_succ]
      push_cast
      field_simp
    · rw [if_neg hi, dif_neg hi, mul_zero, mul_zero]
  · rw [if_neg hu, if_neg hu]

/-! ### `eq:raise` on the line-frequency side -/

/-- The index in `Fin 2` of an axis: `0` for rows, `1` for columns. -/
def axisIndex : Axis → Fin 2
  | .horizontal => 0
  | .vertical => 1

@[simp] theorem finAxis_axisIndex (a : Axis) : finAxis (axisIndex a) = a := by
  cases a <;> simp [finAxis, axisIndex]

theorem sum_ite_finAxis {E : Type*} [AddCommMonoid E] (a : Axis) (X : Fin 2 → E) :
    (∑ i : Fin 2, if a = finAxis i then X i else 0) = X (axisIndex a) := by
  cases a <;> simp [Fin.sum_univ_two, finAxis, axisIndex]

theorem coeFn_finset_sum {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    (s : Finset ι) (f : ι → Lp ℂ 2 μ) :
    ⇑(∑ j ∈ s, f j) =ᵐ[μ] fun x => ∑ j ∈ s, (f j : α → ℂ) x := by
  classical
  refine Finset.induction_on s ?_ ?_
  · filter_upwards [Lp.coeFn_zero ℂ 2 μ] with x hx
    rw [Finset.sum_empty, hx, Finset.sum_empty, Pi.zero_apply]
  · intro a s ha ih
    rw [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (f a) (∑ j ∈ s, f j), ih] with x h1 h2
    rw [h1, Pi.add_apply, h2, Finset.sum_insert ha]

/-- The shift of the direction-`i` raising acts in every axis sector as
multiplication by the raising symbol. -/
theorem orderedFourier_orderedRaiseShift (n : ℕ) (p : Fin 2 → ℝ) (i : Fin 2)
    (c : OrderedCoefficient n) (τ : Fin n → Axis) :
    ((orderedFourier n (orderedRaiseShift n p i c)) τ : UnitAddTorus (Fin n) → ℂ)
      =ᵐ[LineTorusMeasure n] fun t =>
        raisingSymbol p i τ t * ((orderedFourier n c) τ : UnitAddTorus (Fin n) → ℂ) t := by
  set v : LineFreqL2 n := orderedFourier n c with hv
  have hsmul : ∀ (a : ℂ) (w : LineFreqL2 n),
      ((a • w : LineFreqL2 n) : (Fin n → Axis) → Lp ℂ 2 (LineTorusMeasure n)) τ
        = a • ((w : (Fin n → Axis) → Lp ℂ 2 (LineTorusMeasure n)) τ) := by
    intro a w
    rw [lp.coeFn_smul]
    rfl
  have hsub : ∀ (w w' : LineFreqL2 n),
      ((w - w' : LineFreqL2 n) : (Fin n → Axis) → Lp ℂ 2 (LineTorusMeasure n)) τ
        = ((w : (Fin n → Axis) → Lp ℂ 2 (LineTorusMeasure n)) τ)
          - ((w' : (Fin n → Axis) → Lp ℂ 2 (LineTorusMeasure n)) τ) := by
    intro w w'
    rw [lp.coeFn_sub]
    rfl
  have hshift : ∀ (x : Operator.Lattice) (w : LineFreqL2 n),
      ((freqShift n x w : LineFreqL2 n) : (Fin n → Axis) → Lp ℂ 2 (LineTorusMeasure n)) τ
        = charMul n (lineShiftVector n x τ)
            ((w : (Fin n → Axis) → Lp ℂ 2 (LineTorusMeasure n)) τ) := by
    intro x w
    rw [freqShift, l2CongrRightDep_apply]
  have hF : orderedFourier n (orderedRaiseShift n p i c)
      = (2 : ℂ)⁻¹ • (Complex.exp (Complex.I * p i) • freqShift n (Operator.axisVector i) v -
          Complex.exp (-Complex.I * p i) • freqShift n (-Operator.axisVector i) v) := by
    rw [orderedRaiseShift]
    simp only [smul_apply, sub_apply, LinearIsometryEquiv.coe_toLinearIsometry,
      LinearIsometry.coe_toContinuousLinearMap, map_smul, map_sub,
      orderedFourier_orderedTranslate, hv]
  have hsector : (orderedFourier n (orderedRaiseShift n p i c)) τ
      = (2 : ℂ)⁻¹ • (Complex.exp (Complex.I * p i) •
            charMul n (patternShift i τ) (v τ) -
          Complex.exp (-Complex.I * p i) •
            charMul n (-patternShift i τ) (v τ)) := by
    rw [hF, hsmul, hsub, hsmul, hsmul, hshift, hshift, lineShiftVector_eq_patternShift,
      lineShiftVector_neg, lineShiftVector_eq_patternShift]
  rw [hsector]
  filter_upwards [Lp.coeFn_smul ((2 : ℂ)⁻¹)
      (Complex.exp (Complex.I * p i) • charMul n (patternShift i τ) (v τ) -
        Complex.exp (-Complex.I * p i) • charMul n (-patternShift i τ) (v τ)),
    Lp.coeFn_sub (Complex.exp (Complex.I * p i) • charMul n (patternShift i τ) (v τ))
      (Complex.exp (-Complex.I * p i) • charMul n (-patternShift i τ) (v τ)),
    Lp.coeFn_smul (Complex.exp (Complex.I * p i)) (charMul n (patternShift i τ) (v τ)),
    Lp.coeFn_smul (Complex.exp (-Complex.I * p i)) (charMul n (-patternShift i τ) (v τ)),
    coeFn_charMul n (patternShift i τ) (v τ),
    coeFn_charMul n (-patternShift i τ) (v τ)] with t h1 h2 h3 h4 h5 h6
  rw [h1, Pi.smul_apply, h2, Pi.sub_apply, h3, h4, Pi.smul_apply, Pi.smul_apply, h5, h6,
    raisingSymbol]
  simp only [smul_eq_mul]
  ring

/-- The raising symbol is `i sin(P_i)` at the total frequency. -/
theorem raisingSymbol_eq_sin (n : ℕ) (p : Fin 2 → ℝ) (i : Fin 2) (τ : Fin n → Axis)
    (t : UnitAddTorus (Fin n)) :
    raisingSymbol p i τ t = Complex.I * (Real.sin (totalFrequency n p τ t i) : ℂ) := by
  have ht : t = fun a => ((torusLift (t a) : ℝ) : UnitAddCircle) := by
    funext a
    rw [torusLift_coe]
  have hfreq : totalFrequency n p τ t i
      = p i + 2 * Real.pi * ∑ a : Fin n, ((axisShift i (τ a) : ℤ) : ℝ) * torusLift (t a) := by
    simp only [totalFrequency, lineFrequency, lineShiftVector_eq_axisShift]
  rw [show raisingSymbol p i τ t
      = raisingSymbol p i τ (fun a => ((torusLift (t a) : ℝ) : UnitAddCircle)) from
    congrArg _ ht, raisingSymbol_apply, hfreq]

/-- Deleting a line of axis `i` does not change the `i`-th total frequency,
because the frequency of a line of axis `i` has vanishing `i`-th component. -/
theorem totalFrequency_removeNth {n : ℕ} (p : Fin 2 → ℝ) (σ : Fin (n + 1) → Axis)
    (θ : UnitAddTorus (Fin (n + 1))) (r : Fin (n + 1)) (i : Fin 2) (hσ : σ r = finAxis i) :
    totalFrequency n p (Fin.removeNth r σ) (Fin.removeNth r θ) i =
      totalFrequency (n + 1) p σ θ i := by
  have h := totalFrequency_insertNth p i r (Fin.removeNth r σ) (θ r) (Fin.removeNth r θ) i
  rw [axisShift_finAxis_self, ← hσ, Fin.insertNth_self_removeNth,
    Fin.insertNth_self_removeNth] at h
  rw [h]
  simp

/-- **`eq:raise`** (`manuscript.tex:1182`).  In the sector of axis pattern `σ`,
the line-frequency coefficient of `D̃_n c` at `θ` is
`(i/(n+1)) ∑_a sin(P_{σ_a}) ĉ_{σ without a}(θ without a)`, where
`P = totalFrequency (n+1) p σ θ` is the total frequency of the result. -/
theorem orderedFourier_rawRaise (n : ℕ) (p : Fin 2 → ℝ) (c : OrderedCoefficient n)
    (σ : Fin (n + 1) → Axis) :
    ((orderedFourier (n + 1) (rawRaise n p c)) σ : UnitAddTorus (Fin (n + 1)) → ℂ)
      =ᵐ[LineTorusMeasure (n + 1)] fun θ =>
        Complex.I / ((n + 1 : ℕ) : ℂ) * ∑ r : Fin (n + 1),
          (Real.sin (totalFrequency (n + 1) p σ θ (axisIndex (σ r))) : ℂ) *
            ((orderedFourier n c) (Fin.removeNth r σ) : UnitAddTorus (Fin n) → ℂ)
              (Fin.removeNth r θ) := by
  set G : Fin (n + 1) → Lp ℂ 2 (LineTorusMeasure (n + 1)) := fun r =>
    torusRemove n r ((orderedFourier n (orderedRaiseShift n p (axisIndex (σ r)) c))
      (Fin.removeNth r σ)) with hG
  have e1 : orderedFourier (n + 1) (rawRaise n p c) = (((n + 1 : ℕ) : ℂ)⁻¹) •
      ∑ i : Fin 2, ∑ r : Fin (n + 1),
        orderedFourier (n + 1) (insertLine n r i (orderedRaiseShift n p i c)) := by
    rw [rawRaise]
    simp only [smul_apply, sum_apply, ContinuousLinearMap.comp_apply, map_smul, map_sum]
  have hsector : (orderedFourier (n + 1) (rawRaise n p c)) σ =
      (((n + 1 : ℕ) : ℂ)⁻¹) • ∑ r : Fin (n + 1), G r := by
    rw [e1, ← freqEval_apply (n + 1) σ, map_smul]
    simp only [map_sum, freqEval_apply, orderedFourier_insertLine_apply]
    rw [Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun r _ => ?_
    exact sum_ite_finAxis (σ r) (fun i => torusRemove n r
      ((orderedFourier n (orderedRaiseShift n p i c)) (Fin.removeNth r σ)))
  have hterm : ∀ r : Fin (n + 1), (G r : UnitAddTorus (Fin (n + 1)) → ℂ)
      =ᵐ[LineTorusMeasure (n + 1)] fun θ =>
        Complex.I * (Real.sin (totalFrequency (n + 1) p σ θ (axisIndex (σ r))) : ℂ) *
          ((orderedFourier n c) (Fin.removeNth r σ) : UnitAddTorus (Fin n) → ℂ)
            (Fin.removeNth r θ) := by
    intro r
    have h1 := coeFn_torusRemove n r
      ((orderedFourier n (orderedRaiseShift n p (axisIndex (σ r)) c)) (Fin.removeNth r σ))
    have h2 := (measurePreserving_removeNthTorus n r).quasiMeasurePreserving.ae_eq_comp
      (orderedFourier_orderedRaiseShift n p (axisIndex (σ r)) c (Fin.removeNth r σ))
    filter_upwards [h1, h2] with θ hθ1 hθ2
    rw [hG]
    simp only at hθ1 ⊢
    rw [hθ1]
    simp only [Function.comp_apply] at hθ2
    rw [hθ2, raisingSymbol_eq_sin, totalFrequency_removeNth p σ θ r _
      (finAxis_axisIndex (σ r)).symm]
  rw [hsector]
  filter_upwards [Lp.coeFn_smul (((n + 1 : ℕ) : ℂ)⁻¹) (∑ r : Fin (n + 1), G r),
    coeFn_finset_sum Finset.univ G, ae_all_iff.mpr hterm] with θ h1 h2 h3
  rw [h1, Pi.smul_apply, h2, smul_eq_mul, Finset.sum_congr rfl fun r _ => h3 r,
    Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [div_eq_mul_inv]
  ring

end

end Manhattan.Paper
