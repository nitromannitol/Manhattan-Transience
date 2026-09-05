import Manhattan.Estimates.Regional
import Manhattan.Glue.ConcreteGreen
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# The concrete Green density

This file exposes the measurable nonnegative fixed-frequency resolvent density
and connects the concrete Green identity to the non-circular regional
integration theorem.

Paper: `manuscript.tex:590-607` and `manuscript.tex:668-681`.
-/

noncomputable section

open ComplexConjugate InnerProductSpace MeasureTheory RCLike Set
open scoped ComplexConjugate ENNReal InnerProduct

namespace Manhattan.Glue

/-- Product coordinates for the real torus representatives. -/
def concreteFrequency (z : ℝ × ℝ) : Fin 2 → ℝ := ![z.1, z.2]

/-- The concrete bounded fiber generator varies continuously in the two
real frequency coordinates. -/
theorem continuous_concreteFiberGenerator :
    Continuous fun z : ℝ × ℝ ↦
      Manhattan.concreteFiberEnvironment.fiberGenerator (concreteFrequency z) := by
  have hS : Continuous fun z : ℝ × ℝ ↦
      Manhattan.concreteFiberS (concreteFrequency z) := by
    rw [show (fun z : ℝ × ℝ ↦ Manhattan.concreteFiberS (concreteFrequency z)) =
      fun z ↦ (2 : ℂ)⁻¹ • ∑ i,
        (Complex.exp (Complex.I * concreteFrequency z i) •
            Manhattan.environmentShift (Manhattan.Operator.axisVector i) +
          Complex.exp (-Complex.I * concreteFrequency z i) •
            Manhattan.environmentShift (-Manhattan.Operator.axisVector i) -
          (2 : ℂ) • ContinuousLinearMap.id ℂ Manhattan.WalshL2) by
        funext z
        exact Manhattan.concreteFiberS_formula (concreteFrequency z)]
    simp only [Fin.sum_univ_two, concreteFrequency, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    fun_prop
  have hA : Continuous fun z : ℝ × ℝ ↦
      Manhattan.concreteFiberA (concreteFrequency z) := by
    rw [show (fun z : ℝ × ℝ ↦ Manhattan.concreteFiberA (concreteFrequency z)) =
      fun z ↦ (2 : ℂ)⁻¹ • ∑ i, Manhattan.originSignMultiplier i ∘L
        (Complex.exp (Complex.I * concreteFrequency z i) •
            Manhattan.environmentShift (Manhattan.Operator.axisVector i) -
          Complex.exp (-Complex.I * concreteFrequency z i) •
            Manhattan.environmentShift (-Manhattan.Operator.axisVector i)) by
        funext z
        exact Manhattan.concreteFiberA_formula (concreteFrequency z)]
    simp only [Fin.sum_univ_two, concreteFrequency, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    fun_prop
  exact hS.add hA

/-- `λI-G_p` as a continuously varying bounded operator. -/
def concreteResolventOperator (lambda : ℝ) (z : ℝ × ℝ) :
    Manhattan.WalshL2 →L[ℂ] Manhattan.WalshL2 :=
  Manhattan.Operator.resolventOperator
    (Manhattan.concreteFiberEnvironment.fiberGenerator (concreteFrequency z)) lambda

theorem continuous_concreteResolventOperator (lambda : ℝ) :
    Continuous (concreteResolventOperator lambda) := by
  unfold concreteResolventOperator Manhattan.Operator.resolventOperator
  exact continuous_const.sub continuous_concreteFiberGenerator

private theorem concrete_minus_eq_resolventOperator (lambda : ℝ)
    (z : ℝ × ℝ) :
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair
        (concreteFrequency z)).minus lambda =
      concreteResolventOperator lambda z := by
  change (((lambda : ℂ) • ContinuousLinearMap.id ℂ Manhattan.WalshL2 -
      Manhattan.concreteFiberEnvironment.fiberS (concreteFrequency z)) -
        Manhattan.concreteFiberEnvironment.fiberA (concreteFrequency z)) =
    (lambda : ℂ) • ContinuousLinearMap.id ℂ Manhattan.WalshL2 -
      (Manhattan.concreteFiberEnvironment.fiberS (concreteFrequency z) +
        Manhattan.concreteFiberEnvironment.fiberA (concreteFrequency z))
  abel

theorem concreteResolventOperator_isInvertible {lambda : ℝ}
    (hlambda : 0 < lambda) (z : ℝ × ℝ) :
    (concreteResolventOperator lambda z).IsInvertible := by
  let P := Manhattan.concreteFiberEnvironment.dissipativeSkewPair
    (concreteFrequency z)
  refine ⟨P.minusEquiv hlambda, ?_⟩
  change P.minus lambda = concreteResolventOperator lambda z
  exact concrete_minus_eq_resolventOperator lambda z

theorem continuous_concreteResolventInverse {lambda : ℝ}
    (hlambda : 0 < lambda) :
    Continuous fun z : ℝ × ℝ ↦ (concreteResolventOperator lambda z).inverse := by
  rw [continuous_iff_continuousAt]
  intro z
  have hinv : ContinuousAt ContinuousLinearMap.inverse
      (concreteResolventOperator lambda z) :=
    ((concreteResolventOperator_isInvertible hlambda z).contDiffAt_map_inverse
      (n := 1)).continuousAt
  simpa only [Function.comp_apply] using
    hinv.comp (continuous_concreteResolventOperator lambda).continuousAt

/-- The concrete density `r_λ(p)`.  The zero branch makes it a total
function of `lambda`; all paper-facing uses are in the positive branch. -/
def concreteGreenDensity (lambda : ℝ) (z : ℝ × ℝ) : ℝ :=
  if 0 < lambda then
    re ⟪Manhattan.walshL2 ∅,
      (concreteResolventOperator lambda z).inverse (Manhattan.walshL2 ∅)⟫_ℂ
  else 0

/-- On the positive branch the total density is exactly the variational
resolvent quadratic form. -/
theorem concreteGreenDensity_eq_resolventQuadratic {lambda : ℝ}
    (hlambda : 0 < lambda) (z : ℝ × ℝ) :
    concreteGreenDensity lambda z =
      (Manhattan.concreteFiberEnvironment.dissipativeSkewPair
        (concreteFrequency z)).resolventQuadratic hlambda
          (Manhattan.walshL2 ∅) := by
  rw [concreteGreenDensity, if_pos hlambda]
  let P := Manhattan.concreteFiberEnvironment.dissipativeSkewPair
    (concreteFrequency z)
  have hinverse : (concreteResolventOperator lambda z).inverse =
      (P.minusEquiv hlambda).symm := by
    rw [← concrete_minus_eq_resolventOperator lambda z]
    change (P.minus lambda).inverse = (P.minusEquiv hlambda).symm
    simpa only using ContinuousLinearMap.inverse_equiv (P.minusEquiv hlambda)
  rw [hinverse]
  rfl

/-- The density is measurable for every value of the total parameter. -/
theorem concreteGreenDensity_measurable (lambda : ℝ) :
    Measurable (concreteGreenDensity lambda) := by
  by_cases hlambda : 0 < lambda
  · rw [show concreteGreenDensity lambda = fun z : ℝ × ℝ ↦
        re ⟪Manhattan.walshL2 ∅,
          (concreteResolventOperator lambda z).inverse (Manhattan.walshL2 ∅)⟫_ℂ by
      funext z
      simp only [concreteGreenDensity, if_pos hlambda]]
    have hvector : Continuous fun z : ℝ × ℝ ↦
        (concreteResolventOperator lambda z).inverse (Manhattan.walshL2 ∅) :=
      (continuous_concreteResolventInverse hlambda).clm_apply continuous_const
    exact (Complex.continuous_re.comp (continuous_const.inner hvector)).measurable
  · rw [show concreteGreenDensity lambda = fun _ : ℝ × ℝ ↦ (0 : ℝ) by
      funext z
      simp [concreteGreenDensity, hlambda]]
    exact measurable_const

/-- Positivity of the real resolvent quadratic form follows from dissipativity
of the concrete generator. -/
theorem concreteGreenDensity_nonneg (lambda : ℝ) (z : ℝ × ℝ) :
    0 ≤ concreteGreenDensity lambda z := by
  by_cases hlambda : 0 < lambda
  · rw [concreteGreenDensity_eq_resolventQuadratic hlambda z]
    let P := Manhattan.concreteFiberEnvironment.dissipativeSkewPair
      (concreteFrequency z)
    let x := (P.minusEquiv hlambda).symm (Manhattan.walshL2 ∅)
    have hx : P.minus lambda x = Manhattan.walshL2 ∅ :=
      P.minus_apply_inverse hlambda (Manhattan.walshL2 ∅)
    have henergy : 0 ≤ re ⟪P.H lambda x, x⟫_ℂ :=
      P.hEnergy_nonneg hlambda.le x
    rw [Manhattan.Operator.DissipativeSkewPair.resolventQuadratic]
    change 0 ≤ re ⟪Manhattan.walshL2 ∅, x⟫_ℂ
    rw [← hx]
    simp only [Manhattan.Operator.DissipativeSkewPair.minus,
      ContinuousLinearMap.sub_apply, inner_sub_left, map_sub, P.re_inner_A_self,
      sub_zero]
    exact henergy
  · simp [concreteGreenDensity, hlambda]

/-- Uniform domination by the elementary driftless resolvent. -/
theorem concreteGreenDensity_le_inv {lambda : ℝ} (hlambda : 0 < lambda)
    (z : ℝ × ℝ) :
    concreteGreenDensity lambda z ≤ 1 / lambda := by
  rw [concreteGreenDensity_eq_resolventQuadratic hlambda z]
  let P := Manhattan.concreteFiberEnvironment.dissipativeSkewPair
    (concreteFrequency z)
  let V := Manhattan.walshL2 ∅
  let x := (P.minusEquiv hlambda).symm V
  have hx : P.minus lambda x = V := P.minus_apply_inverse hlambda V
  have hresolvent : P.resolventQuadratic hlambda V = re ⟪P.H lambda x, x⟫_ℂ := by
    rw [Manhattan.Operator.DissipativeSkewPair.resolventQuadratic]
    change re ⟪V, x⟫_ℂ = re ⟪P.H lambda x, x⟫_ℂ
    rw [← hx]
    simp only [Manhattan.Operator.DissipativeSkewPair.minus,
      ContinuousLinearMap.sub_apply, inner_sub_left, map_sub, P.re_inner_A_self,
      sub_zero]
  have hlower : lambda * ‖x‖ ^ 2 ≤ re ⟪P.H lambda x, x⟫_ℂ :=
    P.hEnergy_lower lambda x
  have hnormV : ‖V‖ = 1 := Manhattan.orthonormal_walshL2.1 ∅
  have hupper : re ⟪P.H lambda x, x⟫_ℂ ≤ ‖x‖ := by
    rw [← hresolvent]
    change re ⟪V, x⟫_ℂ ≤ ‖x‖
    calc
      re ⟪V, x⟫_ℂ ≤ ‖⟪V, x⟫_ℂ‖ := Complex.re_le_norm _
      _ ≤ ‖V‖ * ‖x‖ := norm_inner_le_norm _ _
      _ = ‖x‖ := by rw [hnormV, one_mul]
  rw [hresolvent]
  by_cases hxzero : ‖x‖ = 0
  · rw [hxzero] at hupper
    exact hupper.trans (one_div_pos.mpr hlambda).le
  · have hxpos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg x) (Ne.symm hxzero)
    have hlambdaNorm : lambda * ‖x‖ ≤ 1 := by
      nlinarith
    exact hupper.trans ((le_div_iff₀ hlambda).2 (by simpa [mul_comm] using hlambdaNorm))

private instance finite_torusProductMeasure :
    IsFiniteMeasure Manhattan.Estimates.torusProductMeasure := ⟨by
  rw [Manhattan.Estimates.torusProductMeasure, ← Set.univ_prod_univ,
    Measure.prod_prod, Measure.restrict_apply_univ,
    Manhattan.Estimates.torus]
  exact ENNReal.mul_lt_top measure_Ioc_lt_top measure_Ioc_lt_top⟩

/-- The density is genuinely integrable on the normalized torus, so no
undefined Bochner integral branch enters the Green identity. -/
theorem concreteGreenDensity_integrable {lambda : ℝ} (hlambda : 0 < lambda) :
    Integrable (concreteGreenDensity lambda)
      Manhattan.Estimates.torusProductMeasure := by
  apply Integrable.of_bound
    (concreteGreenDensity_measurable lambda).aestronglyMeasurable (1 / lambda)
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_nonneg (concreteGreenDensity_nonneg lambda z)]
  exact concreteGreenDensity_le_inv hlambda z

private theorem fiberS_eq_concrete
    (D : Manhattan.Operator.FiberEnvironment Manhattan.WalshL2)
    (hshift : D.shift = Manhattan.environmentShift) (p : Fin 2 → ℝ) :
    D.fiberS p = Manhattan.concreteFiberEnvironment.fiberS p := by
  rw [D.fiberS_eq_formula,
    Manhattan.concreteFiberEnvironment.fiberS_eq_formula, hshift]
  rfl

private theorem fiberA_eq_concrete
    (D : Manhattan.Operator.FiberEnvironment Manhattan.WalshL2)
    (hshift : D.shift = Manhattan.environmentShift)
    (homega : D.omega = Manhattan.originSignMultiplier) (p : Fin 2 → ℝ) :
    D.fiberA p = Manhattan.concreteFiberEnvironment.fiberA p := by
  rw [D.fiberA_eq_formula,
    Manhattan.concreteFiberEnvironment.fiberA_eq_formula, hshift, homega]
  rfl

private theorem dissipativeSkewPair_eq_concrete
    (D : Manhattan.Operator.FiberEnvironment Manhattan.WalshL2)
    (hshift : D.shift = Manhattan.environmentShift)
    (homega : D.omega = Manhattan.originSignMultiplier) (p : Fin 2 → ℝ) :
    D.dissipativeSkewPair p =
      Manhattan.concreteFiberEnvironment.dissipativeSkewPair p := by
  let P := D.dissipativeSkewPair p
  let Q := Manhattan.concreteFiberEnvironment.dissipativeSkewPair p
  change P = Q
  have hS : P.S = Q.S := fiberS_eq_concrete D hshift p
  have hA : P.A = Q.A := fiberA_eq_concrete D hshift homega p
  rcases P with ⟨S, A, hSadj, hSnonpos, hAadj⟩
  rcases Q with ⟨S', A', hSadj', hSnonpos', hAadj'⟩
  simpa only [Manhattan.Operator.DissipativeSkewPair.mk.injEq] using
    And.intro hS hA

/-- Conversion between W5B's product-coordinate normalized integral and the
paper's iterated normalized torus notation. -/
theorem normalizedFrequencyIntegral_eq_iterated {f : ℝ × ℝ → ℝ}
    (hf : Integrable f Manhattan.Estimates.torusProductMeasure) :
    Manhattan.Estimates.normalizedFrequencyIntegral f =
      Manhattan.Estimates.torusIntegral (fun p₁ ↦
        Manhattan.Estimates.torusIntegral (fun p₂ ↦ f (p₁, p₂))) := by
  rw [Manhattan.Estimates.normalizedFrequencyIntegral,
    Manhattan.Estimates.normalizedRegionIntegral, setIntegral_univ,
    Manhattan.Estimates.torusProductMeasure]
  change Integrable f
    ((volume.restrict Manhattan.Estimates.torus).prod
      (volume.restrict Manhattan.Estimates.torus)) at hf
  have hf' : Integrable (Function.uncurry fun p₁ p₂ ↦ f (p₁, p₂))
      ((volume.restrict Manhattan.Estimates.torus).prod
        (volume.restrict Manhattan.Estimates.torus)) := by
    simpa [Function.uncurry] using hf
  rw [← MeasureTheory.integral_integral hf']
  simp only [Manhattan.Estimates.torusIntegral, integral_const_mul, smul_eq_mul]
  ring

/-- Equation (9)--(10) with the concrete density and the normalized product
Haar integral used by the regional estimates. -/
theorem concreteGreenIdentity (lambda : ℝ) (hlambda : 0 < lambda) :
    (∫⁻ t in Ici 0,
      ENNReal.ofReal (Real.exp (-lambda * t)) *
        Manhattan.annealedContinuousKernel t 0 0) =
      ENNReal.ofReal
        (Manhattan.Estimates.normalizedFrequencyIntegral
          (concreteGreenDensity lambda)) := by
  obtain ⟨D, hshift, homega, _hgenerator, hidentity⟩ := proposition_generator
  rw [hidentity lambda hlambda]
  congr 1
  rw [normalizedFrequencyIntegral_eq_iterated
    (concreteGreenDensity_integrable hlambda)]
  apply congrArg Manhattan.Estimates.torusIntegral
  funext p₁
  apply congrArg Manhattan.Estimates.torusIntegral
  funext p₂
  rw [concreteGreenDensity_eq_resolventQuadratic hlambda]
  rw [show concreteFrequency (p₁, p₂) = ![p₁, p₂] by rfl]
  rw [dissipativeSkewPair_eq_concrete D hshift homega]

/-- The exact version-2 Proposition 2.2 statement, named outside the frozen
tree so the final provider can accept W6A's proof without importing a draft
anchor. -/
def PropositionFrequencyClaim : Prop :=
  ∃ D : Manhattan.Operator.FiberEnvironment Manhattan.WalshL2,
    D.shift = Manhattan.environmentShift ∧
    D.omega = Manhattan.originSignMultiplier ∧
    ∃ r0 C : ℝ, 0 < r0 ∧ r0 < 1 ∧ 0 ≤ C ∧
      ∀ (lambda : ℝ), ∀ hlambda : 0 < lambda, lambda ≤ 1 →
        ∀ p : Fin 2 → ℝ,
          p 0 ∈ Manhattan.Estimates.torus →
          p 1 ∈ Manhattan.Estimates.torus →
          ∃ g : Manhattan.WalshL2,
            (D.dissipativeSkewPair p).hEnergy lambda g +
                (D.dissipativeSkewPair p).hMinusEnergy
                  hlambda (Manhattan.walshL2 ∅ - D.fiberA p g) ≤
              C * Manhattan.Operator.frequencyMajorant r0 lambda p

/-- The torus-restricted version-2 competitor claim gives the requested
pointwise majorant for the concrete density directly. -/
theorem concreteGreenDensity_frequency_bound_of_competitorV2
    (h : Manhattan.Operator.CompetitorBoundClaimV2
      Manhattan.concreteFiberEnvironment (Manhattan.walshL2 ∅)) :
    ∃ r0 C : ℝ, 0 < r0 ∧ r0 < 1 ∧ 0 ≤ C ∧
      ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 →
        ∀ z : ℝ × ℝ,
          z.1 ∈ Manhattan.Estimates.torus →
          z.2 ∈ Manhattan.Estimates.torus →
          concreteGreenDensity lambda z ≤
            C * Manhattan.Operator.frequencyMajorant r0 lambda
              (concreteFrequency z) := by
  obtain ⟨r0, C, hr0, hr0One, hC, hbound⟩ :=
    Manhattan.Operator.frequency_resolvent_le_of_competitor_v2
      Manhattan.concreteFiberEnvironment (Manhattan.walshL2 ∅) h
  refine ⟨r0, C, hr0, hr0One, hC, ?_⟩
  intro lambda hlambda hlambdaOne z hz₁ hz₂
  rw [concreteGreenDensity_eq_resolventQuadratic hlambda]
  exact hbound lambda hlambda hlambdaOne (concreteFrequency z) hz₁ hz₂

/-- Proposition 2.2 and the one-sided variational inequality give the
pointwise torus majorant for the concrete Green density. -/
theorem concreteGreenDensity_frequency_bound (h : PropositionFrequencyClaim) :
    ∃ r0 C : ℝ, 0 < r0 ∧ r0 < 1 ∧ 0 ≤ C ∧
      ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 →
        ∀ z : ℝ × ℝ,
          z.1 ∈ Manhattan.Estimates.torus →
          z.2 ∈ Manhattan.Estimates.torus →
          concreteGreenDensity lambda z ≤
            C * Manhattan.Operator.frequencyMajorant r0 lambda
              (concreteFrequency z) := by
  obtain ⟨D, hshift, homega, r0, C, hr0, hr0One, hC, hcompetitor⟩ := h
  refine ⟨r0, C, hr0, hr0One, hC, ?_⟩
  intro lambda hlambda hlambdaOne z hz₁ hz₂
  obtain ⟨g, hg⟩ := hcompetitor lambda hlambda hlambdaOne
    (concreteFrequency z) hz₁ hz₂
  rw [concreteGreenDensity_eq_resolventQuadratic hlambda]
  rw [← dissipativeSkewPair_eq_concrete D hshift homega]
  exact ((D.dissipativeSkewPair (concreteFrequency z)).resolventQuadratic_le
    hlambda (Manhattan.walshL2 ∅) g).trans hg

/-- The concrete density instantiates W5B's non-circular three-region
constructor.  Existence is proposition-valued so Proposition 2.2's
existential constants are not eliminated from `Prop` into data. -/
theorem exists_concreteRegionalIntegralBounds (h : PropositionFrequencyClaim) :
    Nonempty (Manhattan.Operator.RegionalIntegralBounds (fun lambda ↦
      Manhattan.Estimates.normalizedFrequencyIntegral
        (concreteGreenDensity lambda))) := by
  obtain ⟨r0, C, hr0, hr0One, hC, hpoint⟩ :=
    concreteGreenDensity_frequency_bound h
  exact ⟨Manhattan.Estimates.regionalIntegralBoundsOfFrequencyBound
    (fun lambda ↦ Manhattan.Estimates.normalizedFrequencyIntegral
      (concreteGreenDensity lambda))
    concreteGreenDensity r0 C hr0 hr0One hC
    concreteGreenDensity_measurable concreteGreenDensity_nonneg
    (fun _lambda _hlambda _hlambdaOne ↦ le_rfl)
    (fun lambda hlambda hlambdaOne z hz₁ hz₂ ↦
      hpoint lambda hlambda hlambdaOne z hz₁ hz₂)⟩

end Manhattan.Glue
