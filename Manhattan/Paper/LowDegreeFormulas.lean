import Manhattan.Paper.LemmaRaiseMultiplier

/-!
# Lemma 3.1: the low-degree raising and lowering formulas

`lem:formulas` (`manuscript.tex:827-841`) lists the actions of `D̃` and `D̃*` in
degrees zero to three, in the shifted variables and in the normalization that
makes the correspondence between coefficients and elements an isometry.  This
file derives them from `eq:raise` at every degree
(`Manhattan.Paper.orderedFourier_rawRaise`).

The lowering operator is the adjoint of the raising operator.  Its formula
integrates over the frequency of a deleted line; `slotIntegral n r` is that
integration, the adjoint of reading an `L²` function of `n` line frequencies as
a function of `n + 1` of them, and `coeFn_slotIntegral` identifies it with the
integral over the frequency in slot `r`.
-/

open MeasureTheory UnitAddTorus
open Manhattan Manhattan.Glue

namespace Manhattan.Paper

noncomputable section

/-! ### Integration over the frequency of one line -/

/-- Integration over the frequency of the line in slot `r`: the adjoint of
`Manhattan.Glue.torusRemove n r`. -/
def slotIntegral (n : ℕ) (r : Fin (n + 1)) :
    Lp ℂ 2 (LineTorusMeasure (n + 1)) →L[ℂ] Lp ℂ 2 (LineTorusMeasure n) :=
  ContinuousLinearMap.adjoint (torusRemove n r).toContinuousLinearMap

theorem inner_slotIntegral (n : ℕ) (r : Fin (n + 1)) (f : Lp ℂ 2 (LineTorusMeasure n))
    (g : Lp ℂ 2 (LineTorusMeasure (n + 1))) :
    inner ℂ f (slotIntegral n r g) = inner ℂ (torusRemove n r f) g := by
  rw [slotIntegral, ContinuousLinearMap.adjoint_inner_right]
  rfl

theorem measurePreserving_slotSplit (n : ℕ) (r : Fin (n + 1)) :
    MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => UnitAddCircle) r)
      (LineTorusMeasure (n + 1))
      ((AddCircle.haarAddCircle : Measure UnitAddCircle).prod (LineTorusMeasure n)) :=
  measurePreserving_piFinSuccAbove
    (fun _ : Fin (n + 1) => (AddCircle.haarAddCircle : Measure UnitAddCircle)) r

theorem integrable_insertNth_comp (n : ℕ) (r : Fin (n + 1))
    {g : UnitAddTorus (Fin (n + 1)) → ℂ} (hg : Integrable g (LineTorusMeasure (n + 1))) :
    Integrable (fun z : UnitAddCircle × UnitAddTorus (Fin n) => g (Fin.insertNth r z.1 z.2))
      ((AddCircle.haarAddCircle : Measure UnitAddCircle).prod (LineTorusMeasure n)) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => UnitAddCircle) r
  have hmp := (measurePreserving_slotSplit n r).symm e
  exact (hmp.integrable_comp_emb e.symm.measurableEmbedding).mpr hg

theorem integral_insertNth_comp (n : ℕ) (r : Fin (n + 1))
    (g : UnitAddTorus (Fin (n + 1)) → ℂ) :
    ∫ z, g (Fin.insertNth r z.1 z.2)
        ∂((AddCircle.haarAddCircle : Measure UnitAddCircle).prod (LineTorusMeasure n)) =
      ∫ θ, g θ ∂(LineTorusMeasure (n + 1)) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => UnitAddCircle) r
  have hmp := (measurePreserving_slotSplit n r).symm e
  exact hmp.integral_comp e.symm.measurableEmbedding g

/-- **`slotIntegral` integrates over the frequency in slot `r`.** -/
theorem coeFn_slotIntegral (n : ℕ) (r : Fin (n + 1)) (g : Lp ℂ 2 (LineTorusMeasure (n + 1))) :
    (slotIntegral n r g : UnitAddTorus (Fin n) → ℂ) =ᵐ[LineTorusMeasure n] fun θ =>
      ∫ t, (g : UnitAddTorus (Fin (n + 1)) → ℂ) (Fin.insertNth r t θ)
        ∂(AddCircle.haarAddCircle : Measure UnitAddCircle) := by
  have hg : Integrable (g : UnitAddTorus (Fin (n + 1)) → ℂ) (LineTorusMeasure (n + 1)) :=
    (Lp.memLp g).integrable one_le_two
  have hgg := integrable_insertNth_comp n r hg
  have hG : Integrable (fun θ : UnitAddTorus (Fin n) =>
      ∫ t, (g : UnitAddTorus (Fin (n + 1)) → ℂ) (Fin.insertNth r t θ)
        ∂(AddCircle.haarAddCircle : Measure UnitAddCircle)) (LineTorusMeasure n) :=
    hgg.integral_prod_right
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
    (fun s _ _ => ((Lp.memLp (slotIntegral n r g)).integrable one_le_two).integrableOn)
    (fun s _ _ => hG.integrableOn) fun A hA hμA => ?_
  rw [← L2.inner_indicatorConstLp_one hA hμA.ne, inner_slotIntegral, L2.inner_def]
  have hind : (indicatorConstLp 2 hA hμA.ne (1 : ℂ) : UnitAddTorus (Fin n) → ℂ)
      =ᵐ[LineTorusMeasure n] A.indicator fun _ => (1 : ℂ) := indicatorConstLp_coeFn
  have hcomp := (measurePreserving_removeNthTorus n r).quasiMeasurePreserving.ae_eq_comp hind
  have h1 : (∫ θ, inner ℂ ((torusRemove n r (indicatorConstLp 2 hA hμA.ne (1 : ℂ)) :
        UnitAddTorus (Fin (n + 1)) → ℂ) θ) ((g : UnitAddTorus (Fin (n + 1)) → ℂ) θ)
        ∂(LineTorusMeasure (n + 1))) =
      ∫ θ, A.indicator (fun _ => (1 : ℂ)) (Fin.removeNth r θ) *
        (g : UnitAddTorus (Fin (n + 1)) → ℂ) θ ∂(LineTorusMeasure (n + 1)) := by
    refine integral_congr_ae ?_
    filter_upwards [coeFn_torusRemove n r (indicatorConstLp 2 hA hμA.ne (1 : ℂ)), hcomp]
      with θ h1 h2
    rw [h1, RCLike.inner_apply]
    simp only [Function.comp_apply] at h2
    rw [h2]
    by_cases hθ : Fin.removeNth r θ ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hθ]
  rw [h1, ← integral_insertNth_comp n r]
  simp only [Fin.removeNth_insertNth]
  have hint : Integrable (fun z : UnitAddCircle × UnitAddTorus (Fin n) =>
      A.indicator (fun _ => (1 : ℂ)) z.2 *
        (g : UnitAddTorus (Fin (n + 1)) → ℂ) (Fin.insertNth r z.1 z.2))
      ((AddCircle.haarAddCircle : Measure UnitAddCircle).prod (LineTorusMeasure n)) := by
    refine hgg.bdd_mul (c := 1)
      (((measurable_const.indicator hA).comp measurable_snd).aestronglyMeasurable) ?_
    filter_upwards with z
    by_cases hz : z.2 ∈ A
    · simp [Set.indicator_of_mem, hz]
    · simp [Set.indicator_of_notMem, hz]
  rw [integral_prod_symm _ hint, ← integral_indicator hA]
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  by_cases hθ : θ ∈ A
  · simp only [Set.indicator_of_mem hθ, one_mul]
  · simp only [Set.indicator_of_notMem hθ, zero_mul, integral_zero]

/-! ### Multiplication by a continuous function is normal -/

theorem inner_contMul_left (n : ℕ) (g : C(UnitAddTorus (Fin n), ℂ))
    (u v : Lp ℂ 2 (LineTorusMeasure n)) :
    inner ℂ (contMul n g u) v = inner ℂ u (contMul n (star g) v) := by
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_contMul g u, coeFn_contMul (star g) v] with t h1 h2
  rw [h1, h2, RCLike.inner_apply, RCLike.inner_apply, ContinuousMap.star_apply, map_mul]
  simp only [RCLike.star_def]
  ring

/-! ### The raising symbol as a continuous function -/

/-- The raising symbol `i sin(P_i)` of the sector `τ`, as a continuous function. -/
def raisingSymbolMap (n : ℕ) (p : Fin 2 → ℝ) (i : Fin 2) (τ : Fin n → Axis) :
    C(UnitAddTorus (Fin n), ℂ) :=
  ⟨raisingSymbol p i τ, by
    unfold raisingSymbol
    exact continuous_const.mul ((continuous_const.mul (mFourier _).continuous).sub
      (continuous_const.mul (mFourier _).continuous))⟩

theorem raisingSymbolMap_apply (n : ℕ) (p : Fin 2 → ℝ) (i : Fin 2) (τ : Fin n → Axis)
    (t : UnitAddTorus (Fin n)) :
    raisingSymbolMap n p i τ t = Complex.I * (Real.sin (totalFrequency n p τ t i) : ℂ) :=
  raisingSymbol_eq_sin n p i τ t

theorem star_raisingSymbolMap_apply (n : ℕ) (p : Fin 2 → ℝ) (i : Fin 2) (τ : Fin n → Axis)
    (t : UnitAddTorus (Fin n)) :
    star (raisingSymbolMap n p i τ) t = -Complex.I * (Real.sin (totalFrequency n p τ t i) : ℂ) := by
  rw [ContinuousMap.star_apply, raisingSymbolMap_apply, RCLike.star_def, map_mul,
    Complex.conj_I, Complex.conj_ofReal]

theorem orderedFourier_orderedRaiseShift_eq (n : ℕ) (p : Fin 2 → ℝ) (i : Fin 2)
    (c : OrderedCoefficient n) (τ : Fin n → Axis) :
    (orderedFourier n (orderedRaiseShift n p i c)) τ =
      contMul n (raisingSymbolMap n p i τ) ((orderedFourier n c) τ) := by
  apply Lp.ext
  filter_upwards [orderedFourier_orderedRaiseShift n p i c τ,
    coeFn_contMul (raisingSymbolMap n p i τ) ((orderedFourier n c) τ)] with t h1 h2
  rw [h1, h2]
  rfl

/-- The sector `σ` of the line-frequency coefficient of `D̃_n c`, as an
identity in `L²`. -/
theorem orderedFourier_rawRaise_sector (n : ℕ) (p : Fin 2 → ℝ) (c : OrderedCoefficient n)
    (σ : Fin (n + 1) → Axis) :
    (orderedFourier (n + 1) (rawRaise n p c)) σ =
      (((n + 1 : ℕ) : ℂ)⁻¹) • ∑ r : Fin (n + 1),
        torusRemove n r (contMul n (raisingSymbolMap n p (axisIndex (σ r)) (Fin.removeNth r σ))
          ((orderedFourier n c) (Fin.removeNth r σ))) := by
  have e1 : orderedFourier (n + 1) (rawRaise n p c) = (((n + 1 : ℕ) : ℂ)⁻¹) •
      ∑ i : Fin 2, ∑ r : Fin (n + 1),
        orderedFourier (n + 1) (insertLine n r i (orderedRaiseShift n p i c)) := by
    rw [rawRaise]
    simp only [smul_apply, sum_apply, ContinuousLinearMap.comp_apply, map_smul, map_sum]
  rw [e1, ← freqEval_apply (n + 1) σ, map_smul]
  simp only [map_sum, freqEval_apply, orderedFourier_insertLine_apply]
  rw [Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [sum_ite_finAxis (σ r) (fun i => torusRemove n r
      ((orderedFourier n (orderedRaiseShift n p i c)) (Fin.removeNth r σ))),
    orderedFourier_orderedRaiseShift_eq]

/-! ### The raw lowering operator `D̃_n*` -/

/-- **The raw lowering operator** `D̃_n*`, the adjoint of `D̃_n` for the
inner products `⟨F, G⟩ = n! ⟨f, g⟩` of `eq:iso`. -/
def rawLower (n : ℕ) (p : Fin 2 → ℝ) :
    OrderedCoefficient (n + 1) →L[ℂ] OrderedCoefficient n :=
  ((n + 1 : ℕ) : ℂ) • ContinuousLinearMap.adjoint (rawRaise n p)

/-- `D̃_n*` is the adjoint of `D̃_n` for the inner products of `eq:iso`. -/
theorem factorial_mul_inner_rawRaise (n : ℕ) (p : Fin 2 → ℝ) (c : OrderedCoefficient n)
    (k : OrderedCoefficient (n + 1)) :
    ((n + 1).factorial : ℂ) * inner ℂ (rawRaise n p c) k =
      (n.factorial : ℂ) * inner ℂ c (rawLower n p k) := by
  rw [rawLower, smul_apply, inner_smul_right, ContinuousLinearMap.adjoint_inner_right,
    Nat.factorial_succ]
  push_cast
  ring

theorem sum_piFinSuccAbove {E : Type*} [AddCommMonoid E] {n : ℕ} (r : Fin (n + 1))
    (F : (Fin (n + 1) → Axis) → E) :
    (∑ σ : Fin (n + 1) → Axis, F σ) =
      ∑ τ : Fin n → Axis, ∑ x : Axis, F (Fin.insertNth r x τ) := by
  have h := Equiv.sum_comp (Fin.insertNthEquiv (fun _ : Fin (n + 1) => Axis) r) F
  rw [← h, Fintype.sum_prod_type, Finset.sum_comm]
  rfl

/-- The line-frequency coefficient of `D̃_n* k` in the sector `τ`. -/
def rawLowerSector (n : ℕ) (p : Fin 2 → ℝ) (v : LineFreqL2 (n + 1)) (τ : Fin n → Axis) :
    Lp ℂ 2 (LineTorusMeasure n) :=
  ∑ r : Fin (n + 1), ∑ x : Axis,
    contMul n (star (raisingSymbolMap n p (axisIndex x) τ))
      (slotIntegral n r (v (Fin.insertNth r x τ)))

/-- The line-frequency coefficient of `D̃_n* k`. -/
def rawLowerFreq (n : ℕ) (p : Fin 2 → ℝ) (v : LineFreqL2 (n + 1)) : LineFreqL2 n :=
  ∑ τ : Fin n → Axis, lp.single 2 τ (rawLowerSector n p v τ)

theorem rawLowerFreq_apply (n : ℕ) (p : Fin 2 → ℝ) (v : LineFreqL2 (n + 1))
    (τ : Fin n → Axis) : rawLowerFreq n p v τ = rawLowerSector n p v τ := by
  classical
  rw [← freqEval_apply n τ, rawLowerFreq, map_sum]
  simp only [freqEval_apply, lp.single_apply]
  rw [Finset.sum_pi_single, if_pos (Finset.mem_univ τ)]

theorem inner_lineFreq (n : ℕ) (v w : LineFreqL2 n) :
    inner ℂ v w = ∑ τ : Fin n → Axis, inner ℂ (v τ) (w τ) := by
  rw [lp.inner_eq_tsum, tsum_fintype]

/-- **The adjoint of `eq:raise`.** -/
theorem orderedFourier_rawLower (n : ℕ) (p : Fin 2 → ℝ) (k : OrderedCoefficient (n + 1)) :
    orderedFourier n (rawLower n p k) = rawLowerFreq n p (orderedFourier (n + 1) k) := by
  apply ext_inner_left ℂ
  intro w
  obtain ⟨c, rfl⟩ : ∃ c, orderedFourier n c = w :=
    ⟨(orderedFourierEquiv n).symm w, by
      rw [← orderedFourierEquiv_apply, LinearIsometryEquiv.apply_symm_apply]⟩
  rw [(orderedFourier n).inner_map_map]
  have hfac : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  have hlow : inner ℂ c (rawLower n p k) =
      ((n + 1 : ℕ) : ℂ) * inner ℂ (rawRaise n p c) k := by
    have h := factorial_mul_inner_rawRaise n p c k
    rw [Nat.factorial_succ] at h
    push_cast at h ⊢
    field_simp at h ⊢
    linear_combination -h
  rw [hlow, ← (orderedFourier (n + 1)).inner_map_map, inner_lineFreq, inner_lineFreq]
  have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  simp only [orderedFourier_rawRaise_sector, inner_smul_left, sum_inner, rawLowerFreq_apply,
    rawLowerSector, inner_sum, map_inv₀, map_natCast]
  rw [Finset.mul_sum]
  simp only [← mul_assoc, mul_inv_cancel₀ hn, one_mul]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [sum_piFinSuccAbove r (fun σ => inner ℂ (torusRemove n r
    (contMul n (raisingSymbolMap n p (axisIndex (σ r)) (Fin.removeNth r σ))
      ((orderedFourier n c) (Fin.removeNth r σ)))) ((orderedFourier (n + 1) k) σ))]
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun x _ => ?_
  simp only [Fin.removeNth_insertNth, Fin.insertNth_apply_same]
  rw [← inner_slotIntegral, inner_contMul_left]

/-! ### Permuting the line frequencies -/

/-- The permutation `θ ↦ θ ∘ π` of the line frequencies. -/
def torusPermMap (n : ℕ) (π : Equiv.Perm (Fin n)) :
    UnitAddTorus (Fin n) ≃ᵐ UnitAddTorus (Fin n) :=
  MeasurableEquiv.arrowCongr' π.symm (MeasurableEquiv.refl UnitAddCircle)

theorem torusPermMap_apply (n : ℕ) (π : Equiv.Perm (Fin n)) (θ : UnitAddTorus (Fin n)) :
    torusPermMap n π θ = θ ∘ π := rfl

theorem measurePreserving_torusPermMap (n : ℕ) (π : Equiv.Perm (Fin n)) :
    MeasurePreserving (torusPermMap n π) (LineTorusMeasure n) (LineTorusMeasure n) :=
  measurePreserving_arrowCongr' (fun _ => (AddCircle.haarAddCircle : Measure UnitAddCircle))
    (fun _ => (AddCircle.haarAddCircle : Measure UnitAddCircle)) π.symm
    (MeasurableEquiv.refl UnitAddCircle) (fun _ => MeasurePreserving.id _)

/-- Composition with a permutation of the line frequencies. -/
def torusPerm (n : ℕ) (π : Equiv.Perm (Fin n)) :
    Lp ℂ 2 (LineTorusMeasure n) →ₗᵢ[ℂ] Lp ℂ 2 (LineTorusMeasure n) :=
  Lp.compMeasurePreservingₗᵢ ℂ (torusPermMap n π) (measurePreserving_torusPermMap n π)

theorem coeFn_torusPerm (n : ℕ) (π : Equiv.Perm (Fin n)) (f : Lp ℂ 2 (LineTorusMeasure n)) :
    (torusPerm n π f : UnitAddTorus (Fin n) → ℂ) =ᵐ[LineTorusMeasure n]
      fun θ => (f : UnitAddTorus (Fin n) → ℂ) (θ ∘ π) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_torusPermMap n π)

theorem torusPerm_symm_apply (n : ℕ) (π : Equiv.Perm (Fin n)) (f : Lp ℂ 2 (LineTorusMeasure n)) :
    torusPerm n π (torusPerm n π.symm f) = f := by
  apply Lp.ext
  have h := (measurePreserving_torusPermMap n π).quasiMeasurePreserving.ae_eq_comp
    (coeFn_torusPerm n π.symm f)
  filter_upwards [coeFn_torusPerm n π (torusPerm n π.symm f), h] with θ h1 h2
  rw [h1]
  simp only [Function.comp_apply, torusPermMap_apply] at h2
  rw [h2]
  congr 1
  funext a
  simp

theorem inner_torusPerm_right (n : ℕ) (π : Equiv.Perm (Fin n))
    (f g : Lp ℂ 2 (LineTorusMeasure n)) :
    inner ℂ f (torusPerm n π g) = inner ℂ (torusPerm n π.symm f) g := by
  conv_lhs => rw [← torusPerm_symm_apply n π f]
  exact (torusPerm n π).inner_map_map _ _

theorem torusPerm_torusRemove (n : ℕ) (π : Equiv.Perm (Fin (n + 1))) {r r' : Fin (n + 1)}
    (h : ∀ θ : UnitAddTorus (Fin (n + 1)), Fin.removeNth r (θ ∘ π) = Fin.removeNth r' θ)
    (f : Lp ℂ 2 (LineTorusMeasure n)) :
    torusPerm (n + 1) π (torusRemove n r f) = torusRemove n r' f := by
  apply Lp.ext
  have hc := (measurePreserving_torusPermMap (n + 1) π).quasiMeasurePreserving.ae_eq_comp
    (coeFn_torusRemove n r f)
  filter_upwards [coeFn_torusPerm (n + 1) π (torusRemove n r f), hc,
    coeFn_torusRemove n r' f] with θ h1 h2 h3
  rw [h1, h3]
  simp only [Function.comp_apply, torusPermMap_apply] at h2
  rw [h2, h θ]

/-- Integrating a permuted function over one slot is integrating the function
over the corresponding slot. -/
theorem slotIntegral_torusPerm (n : ℕ) (π : Equiv.Perm (Fin (n + 1))) {r r' : Fin (n + 1)}
    (h : ∀ θ : UnitAddTorus (Fin (n + 1)), Fin.removeNth r (θ ∘ π.symm) = Fin.removeNth r' θ)
    (k : Lp ℂ 2 (LineTorusMeasure (n + 1))) :
    slotIntegral n r (torusPerm (n + 1) π k) = slotIntegral n r' k := by
  apply ext_inner_left ℂ
  intro f
  rw [inner_slotIntegral, inner_slotIntegral, inner_torusPerm_right,
    torusPerm_torusRemove n π.symm h]

theorem contMul_zero (n : ℕ) (g : C(UnitAddTorus (Fin n), ℂ)) : contMul n g 0 = 0 := by
  simpa using contMul_smul_right 0 g 0

/-! ### Lemma 3.1 -/

/-- The axis patterns of the low-degree coefficients. -/
abbrev rowPattern : Fin 1 → Axis := ![Axis.horizontal]

/-- The axis pattern of a column sign alone. -/
abbrev columnPattern : Fin 1 → Axis := ![Axis.vertical]

/-- Two row signs. -/
abbrev twoRowPattern : Fin 2 → Axis := ![Axis.horizontal, Axis.horizontal]

/-- A row sign and a column sign. -/
abbrev mixedPattern : Fin 2 → Axis := ![Axis.horizontal, Axis.vertical]

/-- **The symmetric coefficient of type `112`** with normalized coefficient
function `k(r, r', β)` of the two row frequencies and the column frequency:
the factor `1/√18` is the normalization of Section 3.4, and the three axis
patterns carry the three positions of the column sign. -/
def type112Freq (k : Lp ℂ 2 (LineTorusMeasure 3)) : LineFreqL2 3 :=
  lp.single 2 ![Axis.horizontal, Axis.horizontal, Axis.vertical]
      ((Real.sqrt 18 : ℂ)⁻¹ • k) +
    lp.single 2 ![Axis.horizontal, Axis.vertical, Axis.horizontal]
      ((Real.sqrt 18 : ℂ)⁻¹ • torusPerm 3 (Equiv.swap 1 2) k) +
    lp.single 2 ![Axis.vertical, Axis.horizontal, Axis.horizontal]
      ((Real.sqrt 18 : ℂ)⁻¹ • torusPerm 3 (finRotate 3) k)

theorem type112Freq_apply (k : Lp ℂ 2 (LineTorusMeasure 3)) (σ : Fin 3 → Axis) :
    type112Freq k σ =
      (if σ = ![Axis.horizontal, Axis.horizontal, Axis.vertical] then
          (Real.sqrt 18 : ℂ)⁻¹ • k else 0) +
        (if σ = ![Axis.horizontal, Axis.vertical, Axis.horizontal] then
          (Real.sqrt 18 : ℂ)⁻¹ • torusPerm 3 (Equiv.swap 1 2) k else 0) +
        (if σ = ![Axis.vertical, Axis.horizontal, Axis.horizontal] then
          (Real.sqrt 18 : ℂ)⁻¹ • torusPerm 3 (finRotate 3) k else 0) := by
  classical
  simp only [type112Freq, lp.coeFn_add, Pi.add_apply, lp.single_apply, Pi.single_apply]

theorem sum_axis {E : Type*} [AddCommMonoid E] (F : Axis → E) :
    (∑ x : Axis, F x) = F Axis.horizontal + F Axis.vertical := by
  rw [show (Finset.univ : Finset Axis) = {Axis.horizontal, Axis.vertical} from rfl,
    Finset.sum_pair (by decide)]

theorem sqrt_eighteen_eq : Real.sqrt 18 = 3 * Real.sqrt 2 := by
  rw [show (18 : ℝ) = 3 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num),
    Real.sqrt_sq (by norm_num)]

/-- **`eq:D2a`** (`manuscript.tex:830-831`).  In the normalization of Section 3.4,
the two-row component of `D̃₂* k` is `-i sin(α) ∫ k(r, r', β) dm(β)`, where
`α` is the second total frequency of the two-row coefficient. -/
theorem lowering_twoRow (p : Fin 2 → ℝ) (k : Lp ℂ 2 (LineTorusMeasure 3)) :
    (((Real.sqrt 2 : ℝ) : ℂ) • rawLowerFreq 2 p (type112Freq k) twoRowPattern :
        UnitAddTorus (Fin 2) → ℂ) =ᵐ[LineTorusMeasure 2] fun θ =>
      -Complex.I * (Real.sin (totalFrequency 2 p twoRowPattern θ 1) : ℂ) *
        ∫ t, (k : UnitAddTorus (Fin 3) → ℂ) (Fin.insertNth 2 t θ)
          ∂(AddCircle.haarAddCircle : Measure UnitAddCircle) := by
  have hsector : rawLowerFreq 2 p (type112Freq k) twoRowPattern =
      ((3 : ℂ) * (Real.sqrt 18 : ℂ)⁻¹) •
        contMul 2 (star (raisingSymbolMap 2 p 1 twoRowPattern)) (slotIntegral 2 2 k) := by
    rw [rawLowerFreq_apply, rawLowerSector, Fin.sum_univ_three]
    simp only [sum_axis, type112Freq_apply]
    have e0 : slotIntegral 2 0 (torusPerm 3 (finRotate 3) k) = slotIntegral 2 2 k :=
      slotIntegral_torusPerm 2 _ (fun θ => by funext a; fin_cases a <;> rfl) k
    have e1 : slotIntegral 2 1 (torusPerm 3 (Equiv.swap 1 2) k) = slotIntegral 2 2 k :=
      slotIntegral_torusPerm 2 _ (fun θ => by funext a; fin_cases a <;> rfl) k
    simp (config := { decide := true }) only [if_true, if_false, add_zero, zero_add,
      map_zero, map_smul, e0, e1]
    simp only [contMul_zero, zero_add, contMul_smul_right,
      show axisIndex Axis.vertical = 1 from rfl]
    module
  rw [hsector]
  filter_upwards [Lp.coeFn_smul ((3 : ℂ) * (Real.sqrt 18 : ℂ)⁻¹)
      (contMul 2 (star (raisingSymbolMap 2 p 1 twoRowPattern)) (slotIntegral 2 2 k)),
    coeFn_contMul (star (raisingSymbolMap 2 p 1 twoRowPattern)) (slotIntegral 2 2 k),
    coeFn_slotIntegral 2 2 k] with θ h2 h3 h4
  rw [Pi.smul_apply, h2, Pi.smul_apply, h3, h4, star_raisingSymbolMap_apply, smul_eq_mul,
    smul_eq_mul, sqrt_eighteen_eq]
  have h2ne : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  push_cast
  field_simp

/-- **`eq:D2b`** (`manuscript.tex:832-833`).  In the normalization of
Section 3.4, the mixed component of `D̃₂* k` is
`-i √2 sin(β) ∫ k(r, r', β) dm(r')`, for a type-`112` coefficient `k`
symmetric in its two row frequencies. -/
theorem lowering_mixed (p : Fin 2 → ℝ) (k : Lp ℂ 2 (LineTorusMeasure 3))
    (hk : torusPerm 3 (Equiv.swap 0 1) k = k) :
    ((2 : ℂ) • rawLowerFreq 2 p (type112Freq k) mixedPattern :
        UnitAddTorus (Fin 2) → ℂ) =ᵐ[LineTorusMeasure 2] fun θ =>
      -Complex.I * (Real.sqrt 2 : ℂ) * (Real.sin (totalFrequency 2 p mixedPattern θ 0) : ℂ) *
        ∫ t, (k : UnitAddTorus (Fin 3) → ℂ) (Fin.insertNth 1 t θ)
          ∂(AddCircle.haarAddCircle : Measure UnitAddCircle) := by
  have hsector : rawLowerFreq 2 p (type112Freq k) mixedPattern =
      ((3 : ℂ) * (Real.sqrt 18 : ℂ)⁻¹) •
        contMul 2 (star (raisingSymbolMap 2 p 0 mixedPattern)) (slotIntegral 2 1 k) := by
    rw [rawLowerFreq_apply, rawLowerSector, Fin.sum_univ_three]
    simp only [sum_axis, type112Freq_apply]
    have e0 : slotIntegral 2 0 k = slotIntegral 2 1 k := by
      conv_lhs => rw [← hk]
      exact slotIntegral_torusPerm 2 _ (fun θ => by funext a; fin_cases a <;> rfl) k
    have e2 : slotIntegral 2 2 (torusPerm 3 (Equiv.swap 1 2) k) = slotIntegral 2 1 k :=
      slotIntegral_torusPerm 2 _ (fun θ => by funext a; fin_cases a <;> rfl) k
    simp (config := { decide := true }) only [if_true, if_false, add_zero, zero_add,
      map_zero, map_smul, e0, e2]
    simp only [contMul_zero, add_zero, contMul_smul_right,
      show axisIndex Axis.horizontal = 0 from rfl]
    module
  rw [hsector]
  filter_upwards [Lp.coeFn_smul ((3 : ℂ) * (Real.sqrt 18 : ℂ)⁻¹)
      (contMul 2 (star (raisingSymbolMap 2 p 0 mixedPattern)) (slotIntegral 2 1 k)),
    coeFn_contMul (star (raisingSymbolMap 2 p 0 mixedPattern)) (slotIntegral 2 1 k),
    coeFn_slotIntegral 2 1 k] with θ h2 h3 h4
  rw [Pi.smul_apply, h2, Pi.smul_apply, h3, h4, star_raisingSymbolMap_apply, smul_eq_mul,
    smul_eq_mul, sqrt_eighteen_eq, Complex.ofReal_mul, Complex.ofReal_ofNat]
  have hsq : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  have hs0 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  have hcoef : (2 : ℂ) * (3 * (3 * (Real.sqrt 2 : ℂ))⁻¹) = (Real.sqrt 2 : ℂ) := by
    rw [mul_inv, ← mul_assoc (3 : ℂ), mul_inv_cancel₀ (by norm_num : (3 : ℂ) ≠ 0), one_mul,
      ← hsq, mul_assoc, mul_inv_cancel₀ hs0, mul_one]
  linear_combination (-Complex.I * (Real.sin (totalFrequency 2 p mixedPattern θ 0) : ℂ) *
    ∫ t, (k : UnitAddTorus (Fin 3) → ℂ) (Fin.insertNth 1 t θ)
      ∂(AddCircle.haarAddCircle : Measure UnitAddCircle)) * hcoef

theorem totalFrequency_zero_eq (p : Fin 2 → ℝ) (θ : UnitAddTorus (Fin 0)) (i : Fin 2) :
    totalFrequency 0 p ![] θ i = p i := by
  simp [totalFrequency, lineFrequency]

theorem totalFrequency_twoRow_zero (p : Fin 2 → ℝ) (θ : UnitAddTorus (Fin 2)) :
    totalFrequency 2 p twoRowPattern θ 0 = p 0 := by
  simp [totalFrequency, lineFrequency, lineShiftVector_axisVector, finAxis, Fin.sum_univ_two]

/-- **`eq:D1`, first formula** (`manuscript.tex:837`).  For a degree-one
coefficient carrying only a row sign, `D₀* f = -i sin(p₁) ∫ f dm`. -/
theorem lowering_degreeOne (p : Fin 2 → ℝ) (c : OrderedCoefficient 1)
    (hc : (orderedFourier 1 c) columnPattern = 0) :
    ((orderedFourier 0 (rawLower 0 p c)) ![] : UnitAddTorus (Fin 0) → ℂ)
      =ᵐ[LineTorusMeasure 0] fun θ =>
        -Complex.I * (Real.sin (p 0) : ℂ) *
          ∫ t, ((orderedFourier 1 c) rowPattern : UnitAddTorus (Fin 1) → ℂ) (Fin.insertNth 0 t θ)
            ∂(AddCircle.haarAddCircle : Measure UnitAddCircle) := by
  rw [orderedFourier_rawLower, rawLowerFreq_apply, rawLowerSector, Fin.sum_univ_one, sum_axis]
  have hv : (orderedFourier 1 c) (Fin.insertNth 0 Axis.vertical ![]) = 0 := by
    rw [show (Fin.insertNth 0 Axis.vertical ![] : Fin 1 → Axis) = columnPattern by
      funext a; fin_cases a; rfl]
    exact hc
  rw [hv, map_zero, contMul_zero, add_zero,
    show (Fin.insertNth 0 Axis.horizontal ![] : Fin 1 → Axis) = rowPattern by
      funext a; fin_cases a; rfl]
  filter_upwards [coeFn_contMul (star (raisingSymbolMap 0 p (axisIndex Axis.horizontal) ![]))
      (slotIntegral 0 0 ((orderedFourier 1 c) rowPattern)),
    coeFn_slotIntegral 0 0 ((orderedFourier 1 c) rowPattern)] with θ h1 h2
  rw [h1, h2, star_raisingSymbolMap_apply, show axisIndex Axis.horizontal = 0 from rfl,
    totalFrequency_zero_eq]

/-- **`eq:D1`, second formula** (`manuscript.tex:838`).  In the normalization
of Section 3.4, the two-row component of `D̃₁ f` is
`(i/√2) sin(p₁) [f(r) + f(r')]`. -/
theorem raising_twoRow (p : Fin 2 → ℝ) (c : OrderedCoefficient 1) :
    (((Real.sqrt 2 : ℝ) : ℂ) • (orderedFourier 2 (rawRaise 1 p c)) twoRowPattern :
        UnitAddTorus (Fin 2) → ℂ) =ᵐ[LineTorusMeasure 2] fun θ =>
      Complex.I / (Real.sqrt 2 : ℂ) * (Real.sin (p 0) : ℂ) *
        (((orderedFourier 1 c) rowPattern : UnitAddTorus (Fin 1) → ℂ) (Fin.removeNth 0 θ) +
          ((orderedFourier 1 c) rowPattern : UnitAddTorus (Fin 1) → ℂ) (Fin.removeNth 1 θ)) := by
  filter_upwards [orderedFourier_rawRaise 1 p c twoRowPattern] with θ h
  rw [Pi.smul_apply, h, Fin.sum_univ_two]
  have hr0 : Fin.removeNth 0 twoRowPattern = rowPattern := by funext a; fin_cases a; rfl
  have hr1 : Fin.removeNth 1 twoRowPattern = rowPattern := by funext a; fin_cases a; rfl
  rw [hr0, hr1, show twoRowPattern 0 = Axis.horizontal from rfl,
    show twoRowPattern 1 = Axis.horizontal from rfl,
    show axisIndex Axis.horizontal = 0 from rfl, totalFrequency_twoRow_zero]
  have hsq : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  have hcoef : (Real.sqrt 2 : ℂ) * 2⁻¹ = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [mul_right_comm, hsq]
    norm_num
  rw [smul_eq_mul, show ((1 + 1 : ℕ) : ℂ) = 2 by norm_num]
  linear_combination (Complex.I * (Real.sin (p 0) : ℂ) *
    (((orderedFourier 1 c) rowPattern : UnitAddTorus (Fin 1) → ℂ) (Fin.removeNth 0 θ) +
      ((orderedFourier 1 c) rowPattern : UnitAddTorus (Fin 1) → ℂ) (Fin.removeNth 1 θ))) * hcoef

/-- **`eq:D1`, third formula** (`manuscript.tex:839`).  In the normalization
of Section 3.4, the mixed component of `D̃₁ f` for a degree-one coefficient
carrying only a row sign is `i sin(r) f(r)`, where `r` is the second total
frequency of the mixed coefficient. -/
theorem raising_mixed (p : Fin 2 → ℝ) (c : OrderedCoefficient 1)
    (hc : (orderedFourier 1 c) columnPattern = 0) :
    ((2 : ℂ) • (orderedFourier 2 (rawRaise 1 p c)) mixedPattern :
        UnitAddTorus (Fin 2) → ℂ) =ᵐ[LineTorusMeasure 2] fun θ =>
      Complex.I * (Real.sin (totalFrequency 2 p mixedPattern θ 1) : ℂ) *
        ((orderedFourier 1 c) rowPattern : UnitAddTorus (Fin 1) → ℂ) (Fin.removeNth 1 θ) := by
  have hzero : ((orderedFourier 1 c) columnPattern : UnitAddTorus (Fin 1) → ℂ)
      =ᵐ[LineTorusMeasure 1] 0 := by
    rw [hc]
    exact Lp.coeFn_zero ℂ 2 (LineTorusMeasure 1)
  have hzero' := (measurePreserving_removeNthTorus 1 0).quasiMeasurePreserving.ae_eq_comp hzero
  filter_upwards [orderedFourier_rawRaise 1 p c mixedPattern, hzero'] with θ h hz
  rw [Pi.smul_apply, h, Fin.sum_univ_two]
  have hr0 : Fin.removeNth 0 mixedPattern = columnPattern := by funext a; fin_cases a; rfl
  have hr1 : Fin.removeNth 1 mixedPattern = rowPattern := by funext a; fin_cases a; rfl
  simp only [Function.comp_apply, Pi.zero_apply] at hz
  rw [hr0, hr1, hz, show mixedPattern 1 = Axis.vertical from rfl,
    show axisIndex Axis.vertical = 1 from rfl, smul_eq_mul]
  ring

end

end Manhattan.Paper
