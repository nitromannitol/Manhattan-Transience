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

end

end Manhattan.Paper
