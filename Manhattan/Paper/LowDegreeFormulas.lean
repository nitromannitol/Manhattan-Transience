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

end

end Manhattan.Paper
