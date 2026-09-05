import Manhattan.Glue.CubicEnergy

/-!
# Transfer between the three-dimensional Fourier torus and the paper's torus

The raw type-`112` correction is a function on `UnitAddTorus (Fin 3)`, because
that is where its Fourier coefficients are taken. Every scalar estimate of
Sections 4 and 5, on the other hand, is written as an iterated normalized
integral over the paper's real torus `(-π,π]`.

This file supplies the bridge. `integral_unitTorus_three` rewrites a bounded
measurable function of the three angle coordinates as the iterated
`Estimates.torusIntegral`, and the remaining lemmas are the linearity,
Fubini, and translation facts used to evaluate such iterated integrals.

Paper: `manuscript.tex:1305-1330`.
-/

open MeasureTheory Set

noncomputable section

namespace Manhattan.Glue

/-- A bounded measurable real function is integrable for a finite measure. -/
theorem integrable_of_bound {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {f : α → ℝ} (hf : Measurable f) {C : ℝ}
    (hb : ∀ x, |f x| ≤ C) : Integrable f μ :=
  Integrable.mono' (integrable_const C) hf.aestronglyMeasurable
    (Filter.Eventually.of_forall (by simpa [Real.norm_eq_abs] using hb))

section Pi

universe u

variable {U : Type u} [MeasureSpace U] [IsProbabilityMeasure (volume : Measure U)]

/-- Iterated integration on a three-fold power of a probability space. -/
theorem integral_pi_three (H : U → U → U → ℝ)
    (hH : Measurable fun z : U × U × U => H z.1 z.2.1 z.2.2)
    {C : ℝ} (hb : ∀ u v w, |H u v w| ≤ C) :
    (∫ x : Fin 3 → U, H (x 0) (x 1) (x 2)) = ∫ u, ∫ v, ∫ w, H u v w := by
  have step1 : (∫ x : Fin 3 → U, H (x 0) (x 1) (x 2))
      = ∫ y : U × (Fin 2 → U), H y.1 (y.2 0) (y.2 1) :=
    (MeasureTheory.volume_preserving_piFinSuccAbove
      (fun _ : Fin 3 => U) 0).integral_comp'
      (fun y : U × (Fin 2 → U) => H y.1 (y.2 0) (y.2 1))
  have hmeas1 : Measurable fun y : U × (Fin 2 → U) => H y.1 (y.2 0) (y.2 1) := by
    have hcomp : (fun y : U × (Fin 2 → U) => H y.1 (y.2 0) (y.2 1))
        = (fun z : U × U × U => H z.1 z.2.1 z.2.2) ∘
          (fun y : U × (Fin 2 → U) => (y.1, y.2 0, y.2 1)) := rfl
    rw [hcomp]
    exact hH.comp (measurable_fst.prodMk
      (((measurable_pi_apply 0).comp measurable_snd).prodMk
        ((measurable_pi_apply 1).comp measurable_snd)))
  have hint1 : Integrable (fun y : U × (Fin 2 → U) => H y.1 (y.2 0) (y.2 1))
      (volume.prod volume) :=
    integrable_of_bound hmeas1 (fun _ => hb _ _ _)
  rw [step1]
  refine Eq.trans (integral_prod _ hint1) ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only []
  have step2 : (∫ x : Fin 2 → U, H u (x 0) (x 1))
      = ∫ y : U × (Fin 1 → U), H u y.1 (y.2 0) :=
    (MeasureTheory.volume_preserving_piFinSuccAbove
      (fun _ : Fin 2 => U) 0).integral_comp'
      (fun y : U × (Fin 1 → U) => H u y.1 (y.2 0))
  have hmeas2 : Measurable fun y : U × (Fin 1 → U) => H u y.1 (y.2 0) := by
    have hcomp : (fun y : U × (Fin 1 → U) => H u y.1 (y.2 0))
        = (fun z : U × U × U => H z.1 z.2.1 z.2.2) ∘
          (fun y : U × (Fin 1 → U) => (u, y.1, y.2 0)) := rfl
    rw [hcomp]
    exact hH.comp (measurable_const.prodMk (measurable_fst.prodMk
      ((measurable_pi_apply 0).comp measurable_snd)))
  have hint2 : Integrable (fun y : U × (Fin 1 → U) => H u y.1 (y.2 0))
      (volume.prod volume) :=
    integrable_of_bound hmeas2 (fun _ => hb _ _ _)
  rw [step2]
  refine Eq.trans (integral_prod _ hint2) ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  have h := (MeasureTheory.measurePreserving_piUnique
    (fun _ : Fin 1 => (volume : Measure U))).integral_comp' (fun w => H u v w)
  simpa using h

end Pi

attribute [local instance] Real.fact_zero_lt_one

/-- The angle representative of a point of the fundamental domain. -/
theorem unitTorusAngle_coe {a : ℝ}
    (ha : a ∈ Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1)) :
    unitTorusAngle (a : UnitAddCircle) = 2 * Real.pi * a := by
  unfold unitTorusAngle
  congr 1
  change ((AddCircle.equivIoc (1 : ℝ) (-(1 / 2 : ℝ))) (a : UnitAddCircle) : ℝ) = a
  rw [AddCircle.equivIoc_coe_eq ha]

/-- Normalized Haar measure on the unit circle is the paper's normalized
torus measure, read through the angle coordinate. -/
theorem integral_haarAddCircle_angle (g : ℝ → ℝ) :
    (∫ x : UnitAddCircle, g (unitTorusAngle x) ∂AddCircle.haarAddCircle) =
      Estimates.torusIntegral g := by
  rw [AddCircle.integral_haarAddCircle, inv_one, one_smul,
    ← AddCircle.integral_preimage (1 : ℝ) (-(1 / 2 : ℝ))]
  rw [setIntegral_congr_fun measurableSet_Ioc
    (f := fun a : ℝ => g (unitTorusAngle (a : UnitAddCircle)))
    (g := fun a : ℝ => g (2 * Real.pi * a))
    (fun a ha => by simpa using congrArg g (unitTorusAngle_coe ha))]
  have hle : (-(1 / 2 : ℝ)) ≤ -(1 / 2 : ℝ) + 1 := by norm_num
  rw [← intervalIntegral.integral_of_le hle,
    intervalIntegral.integral_comp_mul_left g (c := 2 * Real.pi) (by positivity)]
  rw [Estimates.torusIntegral, Estimates.torus,
    ← intervalIntegral.integral_of_le
      (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
  norm_num
  ring_nf

attribute [local instance] cubicUnitAddCircleMeasureSpace

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The same statement for the ambient measure of the Fourier torus. -/
theorem integral_unitAddCircle_angle (g : ℝ → ℝ) :
    (∫ x : UnitAddCircle, g (unitTorusAngle x)) = Estimates.torusIntegral g :=
  integral_haarAddCircle_angle g

/-- A bounded measurable function of the three angle coordinates integrates
over the Fourier torus as the iterated normalized torus integral. -/
theorem integral_unitTorus_three (F : ℝ → ℝ → ℝ → ℝ)
    (hF : Measurable fun z : ℝ × ℝ × ℝ => F z.1 z.2.1 z.2.2)
    {C : ℝ} (hb : ∀ r r' b, |F r r' b| ≤ C) :
    (∫ x : UnitAddTorus (Fin 3),
        F (unitTorusAngle (x 0)) (unitTorusAngle (x 1)) (unitTorusAngle (x 2)))
      = Estimates.torusIntegral fun r => Estimates.torusIntegral fun r' =>
          Estimates.torusIntegral fun b => F r r' b := by
  have hmeasA : Measurable unitTorusAngle := unitTorusAngle_measurable
  have hH : Measurable fun z : UnitAddCircle × UnitAddCircle × UnitAddCircle =>
      F (unitTorusAngle z.1) (unitTorusAngle z.2.1) (unitTorusAngle z.2.2) :=
    hF.comp ((hmeasA.comp measurable_fst).prodMk
      (((hmeasA.comp measurable_fst).comp measurable_snd).prodMk
        ((hmeasA.comp measurable_snd).comp measurable_snd)))
  rw [integral_pi_three (U := UnitAddCircle)
    (fun u v w => F (unitTorusAngle u) (unitTorusAngle v) (unitTorusAngle w))
    hH (C := C) (fun _ _ _ => hb _ _ _)]
  simp only [integral_unitAddCircle_angle]
  have h2 : ∀ u : UnitAddCircle,
      (∫ v : UnitAddCircle,
          Estimates.torusIntegral (F (unitTorusAngle u) (unitTorusAngle v)))
        = Estimates.torusIntegral (fun r' =>
            Estimates.torusIntegral fun b => F (unitTorusAngle u) r' b) :=
    fun u => integral_unitAddCircle_angle (fun r' =>
      Estimates.torusIntegral fun b => F (unitTorusAngle u) r' b)
  simp only [h2]
  exact integral_unitAddCircle_angle (fun r => Estimates.torusIntegral fun r' =>
    Estimates.torusIntegral fun b => F r r' b)


/-! ### Elementary properties of the normalized torus integral -/

instance torusRestrictFinite :
    IsFiniteMeasure (volume.restrict Estimates.torus) := by
  constructor
  rw [Measure.restrict_apply_univ]
  simp [Estimates.torus]

theorem volume_torus_univ :
    (volume.restrict Estimates.torus) univ = ENNReal.ofReal (2 * Real.pi) := by
  rw [Measure.restrict_apply_univ, Estimates.torus, Real.volume_Ioc]
  congr 1
  ring

theorem volume_torus_real :
    (volume.restrict Estimates.torus).real univ = 2 * Real.pi := by
  rw [Measure.real, volume_torus_univ,
    ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ 2 * Real.pi)]

theorem cubicTorusIntegral_const_mul (c : ℝ) (f : ℝ → ℝ) :
    Estimates.torusIntegral (fun x => c * f x) =
      c * Estimates.torusIntegral f := by
  unfold Estimates.torusIntegral
  rw [integral_const_mul]
  simp only [smul_eq_mul]
  ring

/-- A pointwise bound survives the normalized torus integral. -/
theorem abs_torusIntegral_le {f : ℝ → ℝ} {C : ℝ}
    (hb : ∀ x, |f x| ≤ C) : |Estimates.torusIntegral f| ≤ C := by
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hb 0)
  unfold Estimates.torusIntegral
  simp only [smul_eq_mul, abs_mul]
  have hnorm : ‖∫ x in Estimates.torus, f x‖ ≤ C * (2 * Real.pi) := by
    have h := norm_integral_le_of_norm_le_const
      (μ := volume.restrict Estimates.torus) (C := C) (f := f)
      (Filter.Eventually.of_forall (by simpa [Real.norm_eq_abs] using hb))
    rwa [volume_torus_real] at h
  rw [abs_of_pos (by positivity : (0:ℝ) < (2 * Real.pi)⁻¹)]
  rw [Real.norm_eq_abs] at hnorm
  calc (2 * Real.pi)⁻¹ * |∫ x in Estimates.torus, f x| ≤
      (2 * Real.pi)⁻¹ * (C * (2 * Real.pi)) :=
        mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = C := by field_simp

theorem cubicTorusIntegral_add {f g : ℝ → ℝ}
    (hf : Integrable f (volume.restrict Estimates.torus))
    (hg : Integrable g (volume.restrict Estimates.torus)) :
    Estimates.torusIntegral (fun x => f x + g x) =
      Estimates.torusIntegral f + Estimates.torusIntegral g := by
  unfold Estimates.torusIntegral
  rw [integral_add hf hg, smul_add]

/-- Fubini for two normalized torus integrals. -/
theorem cubicTorusIntegral_swap (f : ℝ → ℝ → ℝ)
    (hf : Integrable (Function.uncurry f)
      ((volume.restrict Estimates.torus).prod
        (volume.restrict Estimates.torus))) :
    (Estimates.torusIntegral fun x => Estimates.torusIntegral fun y => f x y) =
      Estimates.torusIntegral fun y => Estimates.torusIntegral fun x => f x y := by
  unfold Estimates.torusIntegral
  simp only [smul_eq_mul, integral_const_mul]
  rw [← mul_assoc, ← mul_assoc]
  congr 1
  exact integral_integral_swap hf

/-- Translation invariance of the normalized torus integral for a function
supported in a short interval around the origin. -/
theorem torusIntegral_translate {h : ℝ → ℝ} {c rho : ℝ}
    (hpi : 3 * rho < Real.pi) (hc : |c| ≤ rho)
    (hsupp : ∀ s, s ∉ Icc (-rho) 0 → h s = 0) :
    (Estimates.torusIntegral fun r' => h (c + r')) =
      Estimates.torusIntegral h := by
  have hzero : ∀ d : ℝ, |d| ≤ rho → ∀ r' : ℝ,
      r' ∉ Estimates.torus → h (d + r') = 0 := by
    intro d hd r' hr'
    have hdabs := abs_le.mp hd
    apply hsupp
    rw [Estimates.torus, mem_Ioc, not_and_or] at hr'
    intro hmem
    rw [mem_Icc] at hmem
    rcases hr' with hlow | hhigh
    · have hle : r' ≤ -Real.pi := le_of_not_gt hlow
      have : d + r' < -rho := by linarith [hdabs.1, hdabs.2]
      linarith [hmem.1]
    · have hgt : Real.pi < r' := lt_of_not_ge hhigh
      have : 0 < d + r' := by linarith [hdabs.1, hdabs.2]
      linarith [hmem.2]
  unfold Estimates.torusIntegral
  congr 1
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun r' hr' => hzero c hc r' hr'),
    setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun r' hr' => by
        simpa using hzero 0 (by simpa using le_trans (abs_nonneg c) hc) r' hr')]
  exact integral_add_left_eq_self h c

/-- Measurability of an inner normalized torus integral in the outer
variables. -/
theorem torusIntegral_measurable_prod {f : ℝ × ℝ → ℝ → ℝ}
    (hf : Measurable fun z : (ℝ × ℝ) × ℝ => f z.1 z.2) :
    Measurable fun z : ℝ × ℝ => Estimates.torusIntegral fun b => f z b := by
  unfold Estimates.torusIntegral
  simp only [smul_eq_mul]
  exact hf.stronglyMeasurable.integral_prod_right.measurable.const_mul
    (2 * Real.pi)⁻¹

end Manhattan.Glue

end
