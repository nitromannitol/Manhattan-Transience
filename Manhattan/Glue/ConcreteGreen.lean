import Manhattan.Estimates.Elementary
import Manhattan.Model.FiberInstance
import Manhattan.Model.Subordination
import Manhattan.Operator.Semigroup
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Function.Holder

/-!
# The concrete Green identity

This module connects the Poisson-subordinated return kernel to the resolvent
of the concrete Walsh fiber. The support proof is deliberately kept in the
Glue module: the model layer constructs the fair-coin environment and its Walsh
operators, while the Operator module supplies the bounded resolvent theory.

Paper: `manuscript.tex:555-607`.
-/

noncomputable section

open ComplexConjugate InnerProductSpace MeasureTheory RCLike Set
open scoped BigOperators ComplexConjugate ENNReal InnerProduct

namespace Manhattan.Glue

private def pathReturnCount (n : ℕ) (omega : Manhattan.Environment) : ℝ :=
  ∑ path : Fin n → Manhattan.Axis,
    if Manhattan.followPath omega 0 (List.ofFn path) = 0 then 1 else 0

private theorem measurable_pathReturnCount (n : ℕ) :
    Measurable (pathReturnCount n) := by
  apply Finset.measurable_fun_sum
  intro path _
  exact Measurable.ite
    ((measurableSet_singleton (0 : Manhattan.Site)).preimage
      (Manhattan.measurable_followPath 0 (List.ofFn path)))
    measurable_const measurable_const

private theorem pathReturnCount_nonneg (n : ℕ) (omega : Manhattan.Environment) :
    0 ≤ pathReturnCount n omega := by
  apply Finset.sum_nonneg
  intro path _
  split <;> simp

private theorem pathReturnCount_le (n : ℕ) (omega : Manhattan.Environment) :
    pathReturnCount n omega ≤ 2 ^ n := by
  calc
    pathReturnCount n omega ≤ ∑ _path : Fin n → Manhattan.Axis, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro path _
      split <;> simp
    _ = 2 ^ n := by
      have hcard : Fintype.card Manhattan.Axis = 2 := by decide
      simp [hcard]

private theorem integrable_pathReturnCount (n : ℕ) :
    Integrable (pathReturnCount n) Manhattan.environmentLaw := by
  apply Integrable.of_bound (measurable_pathReturnCount n).aestronglyMeasurable (2 ^ n)
  filter_upwards with omega
  rw [Real.norm_eq_abs, abs_of_nonneg (pathReturnCount_nonneg n omega)]
  exact pathReturnCount_le n omega

private theorem integral_complex_pathReturnCount (n : ℕ) :
    (∫ omega, ∑ path : Fin n → Manhattan.Axis,
        (if Manhattan.followPath omega 0 (List.ofFn path) = 0
          then (1 : ℂ) else 0) ∂Manhattan.environmentLaw) =
      ((∫ omega, pathReturnCount n omega ∂Manhattan.environmentLaw : ℝ) : ℂ) := by
  rw [show (fun omega => ∑ path : Fin n → Manhattan.Axis,
      (if Manhattan.followPath omega 0 (List.ofFn path) = 0
        then (1 : ℂ) else 0)) =
      fun omega => ((pathReturnCount n omega : ℝ) : ℂ) by
    funext omega
    simp only [pathReturnCount, Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro path _
    split <;> simp]
  exact ContinuousLinearMap.integral_comp_comm (L := Complex.ofRealCLM)
    (integrable_pathReturnCount n)

private theorem nStepKernel_real_eq (n : ℕ) (omega : Manhattan.Environment) :
    ((Manhattan.nStepKernel omega n 0 0 : NNReal) : ℝ) =
      (2 : ℝ)⁻¹ ^ n * pathReturnCount n omega := by
  rw [Manhattan.nStepKernel, pathReturnCount]
  norm_num [inv_pow]

private theorem integrable_nStepKernel_real (n : ℕ) :
    Integrable (fun omega => ((Manhattan.nStepKernel omega n 0 0 : NNReal) : ℝ))
      Manhattan.environmentLaw := by
  refine ((integrable_pathReturnCount n).const_mul ((2 : ℝ)⁻¹ ^ n)).congr ?_
  filter_upwards with omega
  exact (nStepKernel_real_eq n omega).symm

private theorem lintegral_nStepKernel_eq (n : ℕ) :
    (∫⁻ omega, (Manhattan.nStepKernel omega n 0 0 : ENNReal)
        ∂Manhattan.environmentLaw) =
      ENNReal.ofReal ((2 : ℝ)⁻¹ ^ n *
        ∫ omega, pathReturnCount n omega ∂Manhattan.environmentLaw) := by
  rw [lintegral_coe_eq_integral _ (integrable_nStepKernel_real n)]
  congr 1
  simp_rw [nStepKernel_real_eq]
  exact integral_const_mul _ _

private theorem integral_pathReturnCount_nonneg (n : ℕ) :
    0 ≤ ∫ omega, pathReturnCount n omega ∂Manhattan.environmentLaw :=
  integral_nonneg fun omega => pathReturnCount_nonneg n omega

private theorem integral_pathReturnCount_le (n : ℕ) :
    (∫ omega, pathReturnCount n omega ∂Manhattan.environmentLaw) ≤ 2 ^ n := by
  calc
    _ ≤ ∫ _omega : Manhattan.Environment, (2 ^ n : ℝ)
          ∂Manhattan.environmentLaw := by
      apply integral_mono (integrable_pathReturnCount n) (integrable_const (2 ^ n))
      exact pathReturnCount_le n
    _ = 2 ^ n := by simp

private theorem poisson_nstep_term_eq (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    Manhattan.rateTwoPoissonWeight t n *
        (∫⁻ omega, (Manhattan.nStepKernel omega n 0 0 : ENNReal)
          ∂Manhattan.environmentLaw) =
      ENNReal.ofReal ((Real.exp (-2 * t) * t ^ n / n.factorial) *
        ∫ omega, pathReturnCount n omega ∂Manhattan.environmentLaw) := by
  rw [Manhattan.rateTwoPoissonWeight_of_nonneg ht, lintegral_nStepKernel_eq]
  rw [← ENNReal.ofReal_mul ProbabilityTheory.poissonPMFReal_nonneg]
  congr 1
  rw [ProbabilityTheory.poissonPMFReal]
  simp only [NNReal.coe_mk]
  rw [mul_pow]
  ring_nf
  rw [mul_assoc, ← mul_pow]
  norm_num

set_option maxHeartbeats 800000 in
private theorem annealedContinuousKernel_eq_ofReal_tsum (t : ℝ) (ht : 0 ≤ t) :
    Manhattan.annealedContinuousKernel t 0 0 =
      ENNReal.ofReal (∑' n : ℕ,
        (Real.exp (-2 * t) * t ^ n / n.factorial) *
          ∫ omega, pathReturnCount n omega ∂Manhattan.environmentLaw) := by
  let a : ℕ → ℝ := fun n =>
    (Real.exp (-2 * t) * t ^ n / n.factorial) *
      ∫ omega, pathReturnCount n omega ∂Manhattan.environmentLaw
  let B : ℕ → ℝ := fun n => Real.exp (-2 * t) * (2 * t) ^ n / n.factorial
  have ha_nonneg (n : ℕ) : 0 ≤ a n := by
    dsimp [a]
    exact mul_nonneg
      (div_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg ht n)) (Nat.cast_nonneg _))
      (integral_pathReturnCount_nonneg n)
  have hB_nonneg (n : ℕ) : 0 ≤ B n := by
    dsimp [B]
    exact div_nonneg
      (mul_nonneg (Real.exp_pos _).le (pow_nonneg (mul_nonneg (by norm_num) ht) n))
      (Nat.cast_nonneg _)
  have ha_le (n : ℕ) : a n ≤ B n := by
    dsimp [a, B]
    calc
      (Real.exp (-2 * t) * t ^ n / n.factorial) *
          ∫ omega, pathReturnCount n omega ∂Manhattan.environmentLaw ≤
        (Real.exp (-2 * t) * t ^ n / n.factorial) * 2 ^ n :=
          mul_le_mul_of_nonneg_left (integral_pathReturnCount_le n)
            (div_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg ht n))
              (Nat.cast_nonneg _))
      _ = Real.exp (-2 * t) * (2 * t) ^ n / n.factorial := by
        rw [mul_pow]
        ring
  have hB : Summable B := by
    simpa only [B, div_eq_mul_inv, mul_assoc] using
      (Real.summable_pow_div_factorial (2 * t)).mul_left (Real.exp (-2 * t))
  have ha : Summable a := Summable.of_nonneg_of_le ha_nonneg ha_le hB
  simp only [Manhattan.annealedContinuousKernel, Manhattan.continuousKernel]
  rw [lintegral_tsum]
  · change (∑' i : ℕ, ∫⁻ omega,
        Manhattan.rateTwoPoissonWeight t i *
          (Manhattan.nStepKernel omega i 0 0 : ENNReal)
          ∂Manhattan.environmentLaw) = ENNReal.ofReal (∑' n, a n)
    rw [ENNReal.ofReal_tsum_of_nonneg ha_nonneg ha]
    apply tsum_congr
    intro n
    rw [lintegral_const_mul _
      ((Manhattan.measurable_nStepKernel n 0 0).coe_nnreal_ennreal)]
    simpa only [a] using poisson_nstep_term_eq t ht n
  · intro n
    exact ((Manhattan.measurable_nStepKernel n 0 0).coe_nnreal_ennreal.const_mul
      (Manhattan.rateTwoPoissonWeight t n)).aemeasurable

private theorem walsh_span_dense :
    Dense (Submodule.span ℂ (Set.range Manhattan.walshL2) : Set Manhattan.WalshL2) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  exact Manhattan.walsh_complete

private theorem continuousLinearMap_ext_walsh
    (T U : Manhattan.WalshL2 →L[ℂ] Manhattan.WalshL2)
    (h : ∀ S : Finset Manhattan.LineIndex,
      T (Manhattan.walshL2 S) = U (Manhattan.walshL2 S)) : T = U := by
  apply ContinuousLinearMap.ext_on walsh_span_dense
  rintro _ ⟨S, rfl⟩
  exact h S

/-- The canonical pullback action of an environment translation on `L²(P)`.
This is private support for identifying the Walsh-basis construction with its
pointwise probabilistic meaning. -/
private noncomputable def pullbackEnvironmentShift
    (x : Manhattan.Operator.Lattice) :
    Manhattan.WalshL2 →L[ℂ] Manhattan.WalshL2 :=
  (Lp.compMeasurePreservingₗᵢ ℂ
    (Manhattan.translateEnvironment (Manhattan.latticeToSite x))
    (Manhattan.measurePreserving_translateEnvironment
      (Manhattan.latticeToSite x))).toContinuousLinearMap

private theorem pullbackEnvironmentShift_apply
    (x : Manhattan.Operator.Lattice) (f : Manhattan.WalshL2) :
    (pullbackEnvironmentShift x f : Manhattan.Environment → ℂ) =ᵐ[
        Manhattan.environmentLaw]
      fun omega => f (Manhattan.translateEnvironment (Manhattan.latticeToSite x) omega) := by
  exact Lp.coeFn_compMeasurePreserving f
    (Manhattan.measurePreserving_translateEnvironment (Manhattan.latticeToSite x))

private theorem pullbackEnvironmentShift_eq_environmentShift
    (x : Manhattan.Operator.Lattice) :
    pullbackEnvironmentShift x = Manhattan.environmentShift x := by
  apply continuousLinearMap_ext_walsh
  intro S
  apply Lp.ext
  have hwalsh := (Manhattan.measurePreserving_translateEnvironment
    (Manhattan.latticeToSite x)).quasiMeasurePreserving.tendsto_ae
      (Manhattan.coeFn_walshL2 S)
  filter_upwards [pullbackEnvironmentShift_apply x (Manhattan.walshL2 S),
    Manhattan.coeFn_environmentShift_walshL2 x S,
    hwalsh] with omega hpull hshift hwalsh
  rw [hpull, hshift, hwalsh]

private theorem environmentShift_apply
    (x : Manhattan.Operator.Lattice) (f : Manhattan.WalshL2) :
    (Manhattan.environmentShift x f : Manhattan.Environment → ℂ) =ᵐ[
        Manhattan.environmentLaw]
      fun omega => f (Manhattan.translateEnvironment (Manhattan.latticeToSite x) omega) := by
  rw [← pullbackEnvironmentShift_eq_environmentShift x]
  exact pullbackEnvironmentShift_apply x f

private theorem coordinateCharacter_memLpTop (i : Fin 2) :
    MemLp (Manhattan.coordinateCharacter (Manhattan.originLine i)) ∞
      Manhattan.environmentLaw := by
  refine memLp_top_of_bound (Manhattan.measurable_coordinateCharacter
    (Manhattan.originLine i)).aestronglyMeasurable 1 ?_
  filter_upwards with omega
  exact le_of_eq (Manhattan.norm_coordinateCharacter (Manhattan.originLine i) omega)

private noncomputable def coordinateCharacterLInf (i : Fin 2) :
    Lp ℂ ∞ Manhattan.environmentLaw :=
  (coordinateCharacter_memLpTop i).toLp
    (Manhattan.coordinateCharacter (Manhattan.originLine i))

private theorem coordinateCharacterLInf_apply (i : Fin 2) :
    (coordinateCharacterLInf i : Manhattan.Environment → ℂ) =ᵐ[
        Manhattan.environmentLaw]
      Manhattan.coordinateCharacter (Manhattan.originLine i) :=
  MemLp.coeFn_toLp (coordinateCharacter_memLpTop i)

/-- Pointwise multiplication by the origin sign, bundled as a bounded map on
`L²(P)` through Hölder multiplication `L∞ × L² → L²`. -/
private noncomputable def pointwiseOriginSignMultiplier (i : Fin 2) :
    Manhattan.WalshL2 →L[ℂ] Manhattan.WalshL2 :=
  (ContinuousLinearMap.lsmul ℂ ℂ).holderL
    Manhattan.environmentLaw (∞ : ℝ≥0∞) (2 : ℝ≥0∞) (2 : ℝ≥0∞)
      (coordinateCharacterLInf i)

private theorem pointwiseOriginSignMultiplier_apply (i : Fin 2)
    (f : Manhattan.WalshL2) :
    (pointwiseOriginSignMultiplier i f : Manhattan.Environment → ℂ) =ᵐ[
        Manhattan.environmentLaw]
      fun omega => Manhattan.coordinateCharacter (Manhattan.originLine i) omega * f omega := by
  filter_upwards [ContinuousLinearMap.coeFn_holder
      (r := (2 : ℝ≥0∞)) (ContinuousLinearMap.lsmul ℂ ℂ)
        (coordinateCharacterLInf i) f,
    coordinateCharacterLInf_apply i] with omega hmul hcoordinate
  simpa [hcoordinate] using hmul

private theorem pointwiseOriginSignMultiplier_eq_originSignMultiplier (i : Fin 2) :
    pointwiseOriginSignMultiplier i = Manhattan.originSignMultiplier i := by
  apply continuousLinearMap_ext_walsh
  intro S
  apply Lp.ext
  filter_upwards [pointwiseOriginSignMultiplier_apply i (Manhattan.walshL2 S),
    Manhattan.coeFn_originSignMultiplier_walshL2 i S,
    Manhattan.coeFn_walshL2 S] with omega hpoint hmultiplier hwalsh
  rw [hpoint, hmultiplier, hwalsh]

private theorem originSignMultiplier_apply (i : Fin 2) (f : Manhattan.WalshL2) :
    (Manhattan.originSignMultiplier i f : Manhattan.Environment → ℂ) =ᵐ[
        Manhattan.environmentLaw]
      fun omega => Manhattan.coordinateCharacter (Manhattan.originLine i) omega * f omega := by
  rw [← pointwiseOriginSignMultiplier_eq_originSignMultiplier i]
  exact pointwiseOriginSignMultiplier_apply i f

/-- One rate-one directed jump in the Fourier fiber. -/
private noncomputable def fiberStep (p : Fin 2 → ℝ) (i : Fin 2) :
    Manhattan.WalshL2 →L[ℂ] Manhattan.WalshL2 :=
  (2 : ℂ)⁻¹ •
    ((Complex.exp (Complex.I * p i) •
        Manhattan.environmentShift (Manhattan.Operator.axisVector i) +
      Complex.exp (-Complex.I * p i) •
        Manhattan.environmentShift (-Manhattan.Operator.axisVector i)) +
      Manhattan.originSignMultiplier i ∘L
        (Complex.exp (Complex.I * p i) •
            Manhattan.environmentShift (Manhattan.Operator.axisVector i) -
          Complex.exp (-Complex.I * p i) •
            Manhattan.environmentShift (-Manhattan.Operator.axisVector i)))

private def signedAxisVector (omega : Manhattan.Environment) (i : Fin 2) :
    Manhattan.Operator.Lattice :=
  (omega (Manhattan.originLine i)).sign • Manhattan.Operator.axisVector i

private noncomputable def stepPhase (p : Fin 2 → ℝ)
    (omega : Manhattan.Environment) (i : Fin 2) : ℂ :=
  match omega (Manhattan.originLine i) with
  | .negative => Complex.exp (-Complex.I * p i)
  | .positive => Complex.exp (Complex.I * p i)

private theorem fiberStep_apply (p : Fin 2 → ℝ) (i : Fin 2)
    (f : Manhattan.WalshL2) :
    (fiberStep p i f : Manhattan.Environment → ℂ) =ᵐ[
        Manhattan.environmentLaw]
      fun omega => stepPhase p omega i *
        f (Manhattan.translateEnvironment
          (Manhattan.latticeToSite (signedAxisVector omega i)) omega) := by
  let ep : ℂ := Complex.exp (Complex.I * p i)
  let em : ℂ := Complex.exp (-Complex.I * p i)
  let xp := Manhattan.Operator.axisVector i
  let xm := -Manhattan.Operator.axisVector i
  let fp := Manhattan.environmentShift xp f
  let fm := Manhattan.environmentShift xm f
  have hfp : (fp : Manhattan.Environment → ℂ) =ᵐ[Manhattan.environmentLaw]
      fun omega => f (Manhattan.translateEnvironment (Manhattan.latticeToSite xp) omega) :=
    environmentShift_apply xp f
  have hfm : (fm : Manhattan.Environment → ℂ) =ᵐ[Manhattan.environmentLaw]
      fun omega => f (Manhattan.translateEnvironment (Manhattan.latticeToSite xm) omega) :=
    environmentShift_apply xm f
  have hep : ((ep • fp : Manhattan.WalshL2) : Manhattan.Environment → ℂ) =ᵐ[
      Manhattan.environmentLaw]
      fun omega => ep * f (Manhattan.translateEnvironment (Manhattan.latticeToSite xp) omega) :=
    (Lp.coeFn_smul ep fp).trans (hfp.const_smul ep)
  have hem : ((em • fm : Manhattan.WalshL2) : Manhattan.Environment → ℂ) =ᵐ[
      Manhattan.environmentLaw]
      fun omega => em * f (Manhattan.translateEnvironment (Manhattan.latticeToSite xm) omega) :=
    (Lp.coeFn_smul em fm).trans (hfm.const_smul em)
  have hplus : (((ep • fp) + (em • fm) : Manhattan.WalshL2) :
      Manhattan.Environment → ℂ) =ᵐ[Manhattan.environmentLaw]
      fun omega => ep * f (Manhattan.translateEnvironment (Manhattan.latticeToSite xp) omega) +
        em * f (Manhattan.translateEnvironment (Manhattan.latticeToSite xm) omega) :=
    (Lp.coeFn_add (ep • fp) (em • fm)).trans (hep.add hem)
  have hminus : (((ep • fp) - (em • fm) : Manhattan.WalshL2) :
      Manhattan.Environment → ℂ) =ᵐ[Manhattan.environmentLaw]
      fun omega => ep * f (Manhattan.translateEnvironment (Manhattan.latticeToSite xp) omega) -
        em * f (Manhattan.translateEnvironment (Manhattan.latticeToSite xm) omega) :=
    (Lp.coeFn_sub (ep • fp) (em • fm)).trans (hep.sub hem)
  have horigin := originSignMultiplier_apply i ((ep • fp) - (em • fm))
  have horigin' :
      (Manhattan.originSignMultiplier i ((ep • fp) - (em • fm)) :
          Manhattan.Environment → ℂ) =ᵐ[Manhattan.environmentLaw]
        fun omega => Manhattan.coordinateCharacter (Manhattan.originLine i) omega *
          (ep * f (Manhattan.translateEnvironment (Manhattan.latticeToSite xp) omega) -
            em * f (Manhattan.translateEnvironment (Manhattan.latticeToSite xm) omega)) :=
    by
      filter_upwards [horigin, hminus] with omega horiginOmega hminusOmega
      rw [horiginOmega, hminusOmega]
  have htotal :
      (((ep • fp) + (em • fm) +
          Manhattan.originSignMultiplier i ((ep • fp) - (em • fm)) :
          Manhattan.WalshL2) : Manhattan.Environment → ℂ) =ᵐ[
            Manhattan.environmentLaw]
        fun omega =>
          (ep * f (Manhattan.translateEnvironment (Manhattan.latticeToSite xp) omega) +
            em * f (Manhattan.translateEnvironment (Manhattan.latticeToSite xm) omega)) +
          Manhattan.coordinateCharacter (Manhattan.originLine i) omega *
            (ep * f (Manhattan.translateEnvironment (Manhattan.latticeToSite xp) omega) -
              em * f (Manhattan.translateEnvironment (Manhattan.latticeToSite xm) omega)) :=
    (Lp.coeFn_add ((ep • fp) + (em • fm))
      (Manhattan.originSignMultiplier i ((ep • fp) - (em • fm)))).trans
        (hplus.add horigin')
  have hscaled := (Lp.coeFn_smul (2 : ℂ)⁻¹
    ((ep • fp) + (em • fm) +
      Manhattan.originSignMultiplier i ((ep • fp) - (em • fm)))).trans
        (htotal.const_smul (2 : ℂ)⁻¹)
  filter_upwards [hscaled] with omega homega
  have homega' :
      ((fiberStep p i f : Manhattan.WalshL2) : Manhattan.Environment → ℂ) omega =
        (2 : ℂ)⁻¹ * (
          ep * f (Manhattan.translateEnvironment (Manhattan.latticeToSite xp) omega) +
            em * f (Manhattan.translateEnvironment (Manhattan.latticeToSite xm) omega) +
          Manhattan.coordinateCharacter (Manhattan.originLine i) omega *
            (ep * f (Manhattan.translateEnvironment (Manhattan.latticeToSite xp) omega) -
              em * f (Manhattan.translateEnvironment (Manhattan.latticeToSite xm) omega))) := by
    simpa only [fiberStep, ep, em, xp, xm, fp, fm,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply, Pi.smul_apply,
      smul_eq_mul] using homega
  rw [homega']
  cases hsign : omega (Manhattan.originLine i) <;>
    simp [stepPhase, signedAxisVector, Manhattan.coordinateCharacter,
      Manhattan.orientationCharacter, Manhattan.Orientation.sign, hsign, xp, xm,
      ep, em, mul_comm] <;>
    ring_nf

private def finOfAxis : Manhattan.Axis → Fin 2
  | .horizontal => 0
  | .vertical => 1

@[simp] private theorem finOfAxis_finAxis (i : Fin 2) :
    finOfAxis (Manhattan.finAxis i) = i := by
  fin_cases i <;> rfl

@[simp] private theorem finAxis_finOfAxis (i : Manhattan.Axis) :
    Manhattan.finAxis (finOfAxis i) = i := by
  cases i <;> rfl

private noncomputable def fiberTransition (p : Fin 2 → ℝ) :
    Manhattan.WalshL2 →L[ℂ] Manhattan.WalshL2 :=
  ∑ i : Manhattan.Axis, fiberStep p (finOfAxis i)

private theorem concreteFiberGenerator_eq_transition_sub (p : Fin 2 → ℝ) :
    Manhattan.concreteFiberEnvironment.fiberGenerator p =
      fiberTransition p - (2 : ℂ) • ContinuousLinearMap.id ℂ Manhattan.WalshL2 := by
  apply ContinuousLinearMap.ext
  intro f
  change (Manhattan.concreteFiberS p + Manhattan.concreteFiberA p) f = _
  rw [Manhattan.concreteFiberS_formula, Manhattan.concreteFiberA_formula]
  rw [fiberTransition,
    show (Finset.univ : Finset Manhattan.Axis) = {.horizontal, .vertical} by decide]
  rw [Finset.sum_insert (by simp), Finset.sum_singleton]
  simp only [fiberStep, Fin.sum_univ_two,
    ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    finOfAxis]
  module

private theorem concreteFiberGenerator_nonpositive (p : Fin 2 → ℝ)
    (f : Manhattan.WalshL2) :
    re ⟪Manhattan.concreteFiberEnvironment.fiberGenerator p f, f⟫_ℂ ≤ 0 := by
  let P := Manhattan.concreteFiberEnvironment.dissipativeSkewPair p
  have hS := P.nonpositive_S f
  have hA := P.re_inner_A_self f
  change re ⟪P.S f + P.A f, f⟫_ℂ ≤ 0
  rw [inner_add_left, map_add, hA, add_zero]
  exact hS

private theorem concreteFiberSemigroup_contract (p : Fin 2 → ℝ) (t : ℝ)
    (ht : 0 ≤ t) :
    ‖Manhattan.Operator.operatorSemigroup
      (Manhattan.concreteFiberEnvironment.fiberGenerator p) t‖ ≤ 1 := by
  let G := Manhattan.concreteFiberEnvironment.fiberGenerator p
  letI : NormedSpace ℝ Manhattan.WalshL2 := NormedSpace.restrictScalars ℝ ℂ Manhattan.WalshL2
  letI : InnerProductSpace ℝ Manhattan.WalshL2 :=
    InnerProductSpace.rclikeToReal ℂ Manhattan.WalshL2
  have hantitone (f : Manhattan.WalshL2) :
      Antitone fun s : ℝ => ‖Manhattan.Operator.operatorSemigroup G s f‖ ^ 2 := by
    apply antitone_of_hasDerivAt_nonpos
    · intro s
      exact (Manhattan.Operator.operatorSemigroup_hasDerivAt G f s).norm_sq
    · intro s
      change 2 * re ⟪Manhattan.Operator.operatorSemigroup G s f,
        G (Manhattan.Operator.operatorSemigroup G s f)⟫_ℂ ≤ 0
      have h := concreteFiberGenerator_nonpositive p
        (Manhattan.Operator.operatorSemigroup G s f)
      rw [inner_re_symm] at h
      exact mul_nonpos_of_nonneg_of_nonpos (by norm_num) h
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => ?_
  have hsquare := hantitone f ht
  change ‖Manhattan.Operator.operatorSemigroup G t f‖ ^ 2 ≤
    ‖Manhattan.Operator.operatorSemigroup G 0 f‖ ^ 2 at hsquare
  rw [show Manhattan.Operator.operatorSemigroup G 0 = 1 by
    simp [Manhattan.Operator.operatorSemigroup]] at hsquare
  simp only [ContinuousLinearMap.one_apply] at hsquare
  change ‖Manhattan.Operator.operatorSemigroup G t f‖ ≤ 1 * ‖f‖
  nlinarith [norm_nonneg (Manhattan.Operator.operatorSemigroup G t f), norm_nonneg f]

private theorem fiberStep_norm_le_two (p : Fin 2 → ℝ) (i : Fin 2) :
    ‖fiberStep p i‖ ≤ 2 := by
  let ep : ℂ := Complex.exp (Complex.I * p i)
  let em : ℂ := Complex.exp (-Complex.I * p i)
  let Tp := ep • Manhattan.environmentShift (Manhattan.Operator.axisVector i)
  let Tm := em • Manhattan.environmentShift (-Manhattan.Operator.axisVector i)
  have hep : ‖ep‖ = 1 := by simp [ep]
  have hem : ‖em‖ = 1 := by
    calc
      ‖em‖ = ‖Complex.exp (Complex.I * ((-p i : ℝ) : ℂ))‖ := by
        congr 2
        simp only [em]
        push_cast
        ring_nf
      _ = 1 := Complex.norm_exp_I_mul_ofReal _
  have hTp : ‖Tp‖ ≤ 1 := by
    calc
      ‖Tp‖ ≤ ‖ep‖ * ‖Manhattan.environmentShift (Manhattan.Operator.axisVector i)‖ :=
        ContinuousLinearMap.opNorm_smul_le _ _
      _ ≤ 1 := by rw [hep, one_mul]; exact Manhattan.environmentShift_norm_le _
  have hTm : ‖Tm‖ ≤ 1 := by
    calc
      ‖Tm‖ ≤ ‖em‖ * ‖Manhattan.environmentShift (-Manhattan.Operator.axisVector i)‖ :=
        ContinuousLinearMap.opNorm_smul_le _ _
      _ ≤ 1 := by rw [hem, one_mul]; exact Manhattan.environmentShift_norm_le _
  have hplus : ‖Tp + Tm‖ ≤ 2 := (norm_add_le _ _).trans (by linarith)
  have hminus : ‖Tp - Tm‖ ≤ 2 := (norm_sub_le _ _).trans (by linarith)
  have homega : ‖Manhattan.originSignMultiplier i ∘L (Tp - Tm)‖ ≤ 2 :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans <| by
      nlinarith [Manhattan.originSignMultiplier_norm_le i, norm_nonneg (Tp - Tm)]
  change ‖(2 : ℂ)⁻¹ • (Tp + Tm + Manhattan.originSignMultiplier i ∘L (Tp - Tm))‖ ≤ 2
  have hhalf : ‖(2 : ℂ)⁻¹‖ = (2 : ℝ)⁻¹ := by norm_num
  calc
    _ ≤ ‖(2 : ℂ)⁻¹‖ *
        ‖Tp + Tm + Manhattan.originSignMultiplier i ∘L (Tp - Tm)‖ :=
      ContinuousLinearMap.opNorm_smul_le _ _
    _ ≤ (2 : ℝ)⁻¹ * (2 + 2) := by
      rw [hhalf]
      exact mul_le_mul_of_nonneg_left
        ((norm_add_le _ _).trans (add_le_add hplus homega)) (by positivity)
    _ = 2 := by norm_num

private theorem fiberTransition_norm_le_four (p : Fin 2 → ℝ) :
    ‖fiberTransition p‖ ≤ 4 := by
  rw [fiberTransition,
    show (Finset.univ : Finset Manhattan.Axis) = {.horizontal, .vertical} by decide,
    Finset.sum_insert (by simp), Finset.sum_singleton]
  exact (norm_add_le _ _).trans <| by
    have h0 := fiberStep_norm_le_two p (finOfAxis .horizontal)
    have h1 := fiberStep_norm_le_two p (finOfAxis .vertical)
    linarith

private theorem concreteFiberSemigroup_apply_eq_tsum (p : Fin 2 → ℝ) (t : ℝ)
    (f : Manhattan.WalshL2) :
    Manhattan.Operator.operatorSemigroup
        (Manhattan.concreteFiberEnvironment.fiberGenerator p) t f =
      ∑' n : ℕ, (Real.exp (-2 * t) * t ^ n / n.factorial : ℝ) •
        ((fiberTransition p) ^ n) f := by
  let Q := fiberTransition p
  let G := Manhattan.concreteFiberEnvironment.fiberGenerator p
  have hG : G = Q - (2 : ℂ) • ContinuousLinearMap.id ℂ Manhattan.WalshL2 :=
    concreteFiberGenerator_eq_transition_sub p
  have hsplit : t • G =
      (-2 * t) • (1 : Manhattan.WalshL2 →L[ℂ] Manhattan.WalshL2) + t • Q := by
    rw [hG]
    apply ContinuousLinearMap.ext
    intro x
    change (t : ℂ) • (Q x - (2 : ℂ) • x) =
      ((-2 * t : ℝ) : ℂ) • x + (t : ℂ) • Q x
    module
  have hcomm : Commute
      ((-2 * t) • (1 : Manhattan.WalshL2 →L[ℂ] Manhattan.WalshL2)) (t • Q) := by
    exact (Commute.one_left (t • Q)).smul_left (-2 * t)
  have hexp : NormedSpace.exp ℝ (t • G) =
      (Real.exp (-2 * t)) • NormedSpace.exp ℝ (t • Q) := by
    rw [hsplit, NormedSpace.exp_add_of_commute hcomm]
    have hscalar : NormedSpace.exp ℝ
        ((-2 * t) • (1 : Manhattan.WalshL2 →L[ℂ] Manhattan.WalshL2)) =
        (Real.exp (-2 * t)) •
          (1 : Manhattan.WalshL2 →L[ℂ] Manhattan.WalshL2) := by
      calc
        _ = NormedSpace.exp ℝ ((algebraMap ℝ
              (Manhattan.WalshL2 →L[ℂ] Manhattan.WalshL2)) (-2 * t)) := by
            rw [Algebra.algebraMap_eq_smul_one]
        _ = algebraMap ℝ (Manhattan.WalshL2 →L[ℂ] Manhattan.WalshL2)
              (NormedSpace.exp ℝ (-2 * t)) :=
            (NormedSpace.algebraMap_exp_comm (-2 * t)).symm
        _ = _ := by
          rw [← Real.exp_eq_exp_ℝ, Algebra.algebraMap_eq_smul_one]
    rw [hscalar]
    simp only [smul_mul_assoc, one_mul]
  rw [Manhattan.Operator.operatorSemigroup, hexp]
  have hsummable : Summable fun n : ℕ =>
      ((n.factorial : ℝ)⁻¹ • (t • Q) ^ n) :=
    by simpa only [NormedSpace.expSeries_apply_eq] using
      (NormedSpace.expSeries_summable (𝕂 := ℝ) (t • Q))
  rw [NormedSpace.exp_eq_tsum]
  simp only [ContinuousLinearMap.smul_apply]
  let ev := ContinuousLinearMap.apply ℂ Manhattan.WalshL2 f
  have hvec : Summable fun n : ℕ => (((n.factorial : ℝ)⁻¹ • (t • Q) ^ n) f) :=
    hsummable.map ev ev.continuous
  have heval := ContinuousLinearMap.map_tsum ev hsummable
  change (∑' n : ℕ, ((n.factorial : ℝ)⁻¹ • (t • Q) ^ n)) f =
    ∑' n : ℕ, (((n.factorial : ℝ)⁻¹ • (t • Q) ^ n) f) at heval
  rw [heval]
  rw [← hvec.tsum_const_smul (Real.exp (-2 * t))]
  apply tsum_congr
  intro n
  simp only [ContinuousLinearMap.smul_apply]
  rw [smul_pow]
  simp only [smul_smul]
  dsimp only [Q]
  simp only [ContinuousLinearMap.smul_apply, smul_smul]
  congr 1
  rw [div_eq_mul_inv]
  ring

private theorem summable_concreteFiberSemigroup_series (p : Fin 2 → ℝ) (t : ℝ)
    (f : Manhattan.WalshL2) :
    Summable fun n : ℕ => (Real.exp (-2 * t) * t ^ n / n.factorial : ℝ) •
      ((fiberTransition p) ^ n) f := by
  let Q := fiberTransition p
  have hops : Summable fun n : ℕ => ((n.factorial : ℝ)⁻¹ • (t • Q) ^ n) := by
    simpa only [NormedSpace.expSeries_apply_eq] using
      (NormedSpace.expSeries_summable (𝕂 := ℝ) (t • Q))
  let ev := ContinuousLinearMap.apply ℂ Manhattan.WalshL2 f
  have hvec : Summable fun n : ℕ => (((n.factorial : ℝ)⁻¹ • (t • Q) ^ n) f) :=
    hops.map ev ev.continuous
  have hscaled := hvec.const_smul (Real.exp (-2 * t))
  refine hscaled.congr fun n => ?_
  simp only [ContinuousLinearMap.smul_apply]
  rw [smul_pow]
  simp only [smul_smul]
  dsimp only [Q]
  simp only [ContinuousLinearMap.smul_apply, smul_smul]
  congr 1
  rw [div_eq_mul_inv]
  ring

private theorem inner_walshEmpty_semigroup_eq_tsum (p : Fin 2 → ℝ) (t : ℝ) :
    inner ℂ (Manhattan.walshL2 ∅)
        (Manhattan.Operator.operatorSemigroup
          (Manhattan.concreteFiberEnvironment.fiberGenerator p) t
          (Manhattan.walshL2 ∅)) =
      ∑' n : ℕ, (Real.exp (-2 * t) * t ^ n / n.factorial : ℝ) •
        inner ℂ (Manhattan.walshL2 ∅)
          (((fiberTransition p) ^ n) (Manhattan.walshL2 ∅)) := by
  rw [concreteFiberSemigroup_apply_eq_tsum]
  let L := innerSL ℂ (Manhattan.walshL2 ∅)
  have hs := summable_concreteFiberSemigroup_series p t (Manhattan.walshL2 ∅)
  have hmap := ContinuousLinearMap.map_tsum L hs
  change inner ℂ (Manhattan.walshL2 ∅)
      (∑' n : ℕ, (Real.exp (-2 * t) * t ^ n / n.factorial : ℝ) •
        ((fiberTransition p) ^ n) (Manhattan.walshL2 ∅)) = _ at hmap
  rw [hmap]
  apply tsum_congr
  intro n
  simp only [L, innerSL_apply_apply, RCLike.real_smul_eq_coe_smul (K := ℂ),
    inner_smul_right, smul_eq_mul]

private def sitePairing (p : Fin 2 → ℝ) (z : Manhattan.Site) : ℝ :=
  p 0 * z.1 + p 1 * z.2

private noncomputable def sitePhase (p : Fin 2 → ℝ) (z : Manhattan.Site) : ℂ :=
  Complex.exp (Complex.I * sitePairing p z)

private theorem sitePairing_add (p : Fin 2 → ℝ) (x y : Manhattan.Site) :
    sitePairing p (x + y) = sitePairing p x + sitePairing p y := by
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  simp only [sitePairing, Prod.fst_add, Prod.snd_add, Int.cast_add]
  ring

private theorem sitePhase_add (p : Fin 2 → ℝ) (x y : Manhattan.Site) :
    sitePhase p (x + y) = sitePhase p x * sitePhase p y := by
  rw [sitePhase, sitePhase, sitePhase, sitePairing_add, Complex.ofReal_add,
    mul_add, Complex.exp_add]

private theorem measurable_pathPhase (p : Fin 2 → ℝ) (path : List Manhattan.Axis) :
    Measurable fun omega : Manhattan.Environment =>
      sitePhase p (Manhattan.followPath omega 0 path) := by
  exact (measurable_of_countable (sitePhase p)).comp
    (Manhattan.measurable_followPath 0 path)

private theorem norm_pathPhase (p : Fin 2 → ℝ) (path : List Manhattan.Axis)
    (omega : Manhattan.Environment) :
    ‖sitePhase p (Manhattan.followPath omega 0 path)‖ = 1 := by
  exact Complex.norm_exp_I_mul_ofReal _

private theorem pathPhase_memLp (p : Fin 2 → ℝ) (path : List Manhattan.Axis) :
    MemLp (fun omega : Manhattan.Environment =>
      sitePhase p (Manhattan.followPath omega 0 path)) 2 Manhattan.environmentLaw := by
  refine MemLp.of_bound (measurable_pathPhase p path).aestronglyMeasurable 1 ?_
  filter_upwards with omega
  exact le_of_eq (norm_pathPhase p path omega)

private noncomputable def pathVector {n : ℕ} (p : Fin 2 → ℝ)
    (path : Fin n → Manhattan.Axis) : Manhattan.WalshL2 :=
  (pathPhase_memLp p (List.ofFn path)).toLp
    (fun omega => sitePhase p (Manhattan.followPath omega 0 (List.ofFn path)))

private theorem pathVector_apply {n : ℕ} (p : Fin 2 → ℝ)
    (path : Fin n → Manhattan.Axis) :
    (pathVector p path : Manhattan.Environment → ℂ) =ᵐ[Manhattan.environmentLaw]
      fun omega => sitePhase p (Manhattan.followPath omega 0 (List.ofFn path)) :=
  MemLp.coeFn_toLp (pathPhase_memLp p (List.ofFn path))

private theorem latticeToSite_signedAxisVector (omega : Manhattan.Environment) (i : Fin 2) :
    Manhattan.latticeToSite (signedAxisVector omega i) =
      (omega (Manhattan.originLine i)).sign • Manhattan.basisStep (Manhattan.finAxis i) := by
  fin_cases i
  · cases hsign : omega (Manhattan.originLine 0) <;>
      simp [signedAxisVector, Manhattan.Operator.axisVector, Manhattan.latticeToSite,
        Manhattan.basisStep, Manhattan.finAxis, Manhattan.Orientation.sign, hsign]
  · cases hsign : omega (Manhattan.originLine 1) <;>
      simp [signedAxisVector, Manhattan.Operator.axisVector, Manhattan.latticeToSite,
        Manhattan.basisStep, Manhattan.finAxis, Manhattan.Orientation.sign, hsign]

private theorem directedNeighbor_zero_eq_signedStep
    (omega : Manhattan.Environment) (i : Fin 2) :
    Manhattan.directedNeighbor omega 0 (Manhattan.finAxis i) =
      Manhattan.latticeToSite (signedAxisVector omega i) := by
  rw [latticeToSite_signedAxisVector]
  simp only [Manhattan.directedNeighbor, zero_add]
  congr 2
  fin_cases i <;>
    simp [Manhattan.lineAt, Manhattan.transverseCoordinate, Manhattan.originLine,
      Manhattan.finAxis]

private theorem stepPhase_mul_pathPhase (p : Fin 2 → ℝ) (i : Fin 2)
    (path : List Manhattan.Axis) (omega : Manhattan.Environment) :
    stepPhase p omega i *
        sitePhase p (Manhattan.followPath
          (Manhattan.translateEnvironment
            (Manhattan.latticeToSite (signedAxisVector omega i)) omega) 0 path) =
      sitePhase p (Manhattan.followPath omega 0 (Manhattan.finAxis i :: path)) := by
  rw [Manhattan.followPath_cons, directedNeighbor_zero_eq_signedStep]
  have hfollow := Manhattan.followPath_translate
    (Manhattan.latticeToSite (signedAxisVector omega i)) 0 omega path
  simp only [add_zero] at hfollow
  rw [hfollow]
  rw [sitePhase_add]
  congr 1
  fin_cases i
  · cases hsign : omega (Manhattan.originLine 0) <;>
      simp [stepPhase, signedAxisVector, sitePhase, sitePairing,
        Manhattan.Operator.axisVector, Manhattan.latticeToSite,
        Manhattan.Orientation.sign, hsign]
  · cases hsign : omega (Manhattan.originLine 1) <;>
      simp [stepPhase, signedAxisVector, sitePhase, sitePairing,
        Manhattan.Operator.axisVector, Manhattan.latticeToSite,
        Manhattan.Orientation.sign, hsign]

private theorem fiberStep_pathVector {n : ℕ} (p : Fin 2 → ℝ) (i : Fin 2)
    (path : Fin n → Manhattan.Axis) :
    fiberStep p i (pathVector p path) = pathVector p (Fin.cons (Manhattan.finAxis i) path) := by
  apply Lp.ext
  have hpathPlus := (Manhattan.measurePreserving_translateEnvironment
    (Manhattan.latticeToSite (Manhattan.Operator.axisVector i))).quasiMeasurePreserving.tendsto_ae
      (pathVector_apply p path)
  have hpathMinus := (Manhattan.measurePreserving_translateEnvironment
    (Manhattan.latticeToSite (-Manhattan.Operator.axisVector i))).quasiMeasurePreserving.tendsto_ae
      (pathVector_apply p path)
  filter_upwards [fiberStep_apply p i (pathVector p path),
    pathVector_apply p (Fin.cons (Manhattan.finAxis i) path),
    hpathPlus, hpathMinus] with omega hstep hcons hplus hminus
  rw [hstep, hcons, List.ofFn_cons]
  cases hsign : omega (Manhattan.originLine i)
  · have hsigned : signedAxisVector omega i = -Manhattan.Operator.axisVector i := by
      simp [signedAxisVector, Manhattan.Orientation.sign, hsign]
    rw [hsigned, hminus]
    simpa only [hsigned] using stepPhase_mul_pathPhase p i (List.ofFn path) omega
  · have hsigned : signedAxisVector omega i = Manhattan.Operator.axisVector i := by
      simp [signedAxisVector, Manhattan.Orientation.sign, hsign]
    rw [hsigned, hplus]
    simpa only [hsigned] using stepPhase_mul_pathPhase p i (List.ofFn path) omega

private theorem pathVector_zero (p : Fin 2 → ℝ) :
    pathVector p (fun i : Fin 0 => i.elim0) = Manhattan.walshL2 ∅ := by
  apply Lp.ext
  filter_upwards [pathVector_apply p (fun i : Fin 0 => i.elim0),
    Manhattan.coeFn_walshL2 ∅] with omega hpath hwalsh
  rw [hpath, hwalsh]
  simp [sitePhase, sitePairing, Manhattan.walshCharacter]

private theorem fiberTransition_pow_walsh (p : Fin 2 → ℝ) (n : ℕ) :
    ((fiberTransition p) ^ n) (Manhattan.walshL2 ∅) =
      ∑ path : Fin n → Manhattan.Axis, pathVector p path := by
  induction n with
  | zero =>
      rw [pow_zero, ContinuousLinearMap.one_apply]
      simpa only [Fintype.sum_unique] using (pathVector_zero p).symm
  | succ n ih =>
      rw [pow_succ', ContinuousLinearMap.mul_apply, ih, map_sum, fiberTransition]
      change (∑ path : Fin n → Manhattan.Axis,
        ∑ i : Manhattan.Axis, fiberStep p (finOfAxis i) (pathVector p path)) = _
      rw [Finset.sum_comm]
      simp_rw [fiberStep_pathVector]
      calc
        ∑ i : Manhattan.Axis, ∑ path : Fin n → Manhattan.Axis,
            pathVector p (Fin.cons (Manhattan.finAxis (finOfAxis i)) path) =
            ∑ q : Manhattan.Axis × (Fin n → Manhattan.Axis),
              pathVector p (Fin.cons q.1 q.2) := by
                simp only [finAxis_finOfAxis, Fintype.sum_prod_type]
        _ = ∑ path : Fin (n + 1) → Manhattan.Axis, pathVector p path := by
          simpa only using
            (Fin.consEquiv (fun _ : Fin (n + 1) => Manhattan.Axis)).sum_comp
              (fun path => pathVector p path)

private theorem inner_walshEmpty_pathVector {n : ℕ} (p : Fin 2 → ℝ)
    (path : Fin n → Manhattan.Axis) :
    inner ℂ (Manhattan.walshL2 ∅) (pathVector p path) =
      ∫ omega, sitePhase p
        (Manhattan.followPath omega 0 (List.ofFn path))
          ∂Manhattan.environmentLaw := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Manhattan.coeFn_walshL2 ∅, pathVector_apply p path] with omega hwalsh hpath
  rw [hwalsh, hpath]
  simp [Manhattan.walshCharacter]

private theorem torusIntegral_character (m : ℤ) :
    Manhattan.Estimates.torusIntegral
        (fun p : ℝ => Complex.exp (Complex.I * ((p * (m : ℝ) : ℝ) : ℂ))) =
      if m = 0 then 1 else 0 := by
  by_cases hm : m = 0
  · subst m
    simp [Manhattan.Estimates.torusIntegral, Manhattan.Estimates.torus]
    rw [max_eq_left]
    · push_cast
      field_simp
      norm_num
    · positivity
  · rw [if_neg hm, Manhattan.Estimates.torusIntegral, Manhattan.Estimates.torus]
    rw [← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
    have hc : Complex.I * (m : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (Int.cast_ne_zero.mpr hm)
    have hinterval :
        (∫ p in -Real.pi..Real.pi,
          Complex.exp (Complex.I * ((p * (m : ℝ) : ℝ) : ℂ))) = 0 := by
      have hintegrand :
          (fun p : ℝ => Complex.exp (Complex.I * ((p * (m : ℝ) : ℝ) : ℂ))) =
            fun p : ℝ => Complex.exp ((Complex.I * (m : ℂ)) * p) := by
        funext p
        congr 1
        push_cast
        ring
      rw [hintegrand, integral_exp_mul_complex hc]
      rw [show ((-Real.pi : ℝ) : ℂ) = -(Real.pi : ℂ) by norm_num]
      have hperiod :
          Complex.exp ((Complex.I * (m : ℂ)) * (Real.pi : ℂ)) =
            Complex.exp ((Complex.I * (m : ℂ)) * (-(Real.pi : ℂ))) := by
        calc
          Complex.exp ((Complex.I * (m : ℂ)) * (Real.pi : ℂ)) =
              Complex.exp ((Complex.I * (m : ℂ)) * (-(Real.pi : ℂ)) +
                (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) := by
                  congr 1
                  ring
          _ = Complex.exp ((Complex.I * (m : ℂ)) * (-(Real.pi : ℂ))) *
                Complex.exp ((m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) :=
              Complex.exp_add _ _
          _ = Complex.exp ((Complex.I * (m : ℂ)) * (-(Real.pi : ℂ))) := by
              rw [Complex.exp_int_mul_two_pi_mul_I]
              simp
      rw [hperiod, sub_self, zero_div]
    rw [hinterval, smul_zero]

private theorem torusIntegral_const_mul (c : ℂ) (f : ℝ → ℂ) :
    Manhattan.Estimates.torusIntegral (fun p => c * f p) =
      c * Manhattan.Estimates.torusIntegral f := by
  simp only [Manhattan.Estimates.torusIntegral, integral_const_mul, Complex.real_smul]
  ring

private theorem torusIntegral_sitePhase (z : Manhattan.Site) :
    Manhattan.Estimates.torusIntegral (fun p₁ : ℝ =>
      Manhattan.Estimates.torusIntegral (fun p₂ : ℝ =>
        sitePhase ![p₁, p₂] z)) = if z = 0 then 1 else 0 := by
  rcases z with ⟨z₁, z₂⟩
  have hsplit (p₁ p₂ : ℝ) :
      sitePhase ![p₁, p₂] (z₁, z₂) =
        Complex.exp (Complex.I * ((p₁ * (z₁ : ℝ) : ℝ) : ℂ)) *
          Complex.exp (Complex.I * ((p₂ * (z₂ : ℝ) : ℝ) : ℂ)) := by
    rw [sitePhase, sitePairing, Complex.ofReal_add, mul_add, Complex.exp_add]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show (fun p₁ : ℝ => Manhattan.Estimates.torusIntegral (fun p₂ : ℝ =>
      sitePhase ![p₁, p₂] (z₁, z₂))) = fun p₁ : ℝ =>
        Complex.exp (Complex.I * ((p₁ * (z₁ : ℝ) : ℝ) : ℂ)) *
          (if z₂ = 0 then 1 else 0) by
    funext p₁
    simp_rw [hsplit p₁]
    rw [torusIntegral_const_mul, torusIntegral_character]]
  by_cases hz₂ : z₂ = 0
  · rw [if_pos hz₂]
    simp only [mul_one, torusIntegral_character]
    by_cases hz₁ : z₁ = 0 <;> simp [hz₁, hz₂]
  · rw [if_neg hz₂]
    simp [hz₂, Manhattan.Estimates.torusIntegral]

private theorem torusIntegral_integral_swap
    (f : ℝ → Manhattan.Environment → ℂ)
    (hf : Integrable (Function.uncurry f)
      ((volume.restrict Manhattan.Estimates.torus).prod Manhattan.environmentLaw)) :
    Manhattan.Estimates.torusIntegral (fun p =>
      ∫ omega, f p omega ∂Manhattan.environmentLaw) =
      ∫ omega, Manhattan.Estimates.torusIntegral (fun p => f p omega)
        ∂Manhattan.environmentLaw := by
  simp only [Manhattan.Estimates.torusIntegral]
  rw [integral_integral_swap hf, integral_smul]

private theorem measurable_joint_pathPhase {n : ℕ}
    (path : Fin n → Manhattan.Axis) :
    Measurable fun q : (ℝ × ℝ) × Manhattan.Environment =>
      sitePhase ![q.1.1, q.1.2]
        (Manhattan.followPath q.2 0 (List.ofFn path)) := by
  let endpoint : Manhattan.Environment → Manhattan.Site := fun omega =>
    Manhattan.followPath omega 0 (List.ofFn path)
  have hendpoint : Measurable endpoint := Manhattan.measurable_followPath 0 (List.ofFn path)
  have hx : Measurable fun q : (ℝ × ℝ) × Manhattan.Environment =>
      ((endpoint q.2).1 : ℝ) :=
    (measurable_of_countable fun z : ℤ => (z : ℝ)).comp
      ((measurable_fst.comp hendpoint).comp measurable_snd)
  have hy : Measurable fun q : (ℝ × ℝ) × Manhattan.Environment =>
      ((endpoint q.2).2 : ℝ) :=
    (measurable_of_countable fun z : ℤ => (z : ℝ)).comp
      ((measurable_snd.comp hendpoint).comp measurable_snd)
  have hp₁ : Measurable fun q : (ℝ × ℝ) × Manhattan.Environment => q.1.1 :=
    measurable_fst.comp measurable_fst
  have hp₂ : Measurable fun q : (ℝ × ℝ) × Manhattan.Environment => q.1.2 :=
    measurable_snd.comp measurable_fst
  exact Complex.continuous_exp.measurable.comp
    (measurable_const.mul (Complex.continuous_ofReal.measurable.comp
      ((hp₁.mul hx).add (hp₂.mul hy))))

private theorem norm_joint_pathPhase {n : ℕ} (path : Fin n → Manhattan.Axis)
    (q : (ℝ × ℝ) × Manhattan.Environment) :
    ‖sitePhase ![q.1.1, q.1.2]
      (Manhattan.followPath q.2 0 (List.ofFn path))‖ = 1 := by
  exact Complex.norm_exp_I_mul_ofReal _

private theorem torusIntegral_inner_pathVector {n : ℕ}
    (path : Fin n → Manhattan.Axis) :
    Manhattan.Estimates.torusIntegral (fun p₁ : ℝ =>
      Manhattan.Estimates.torusIntegral (fun p₂ : ℝ =>
        inner ℂ (Manhattan.walshL2 ∅) (pathVector ![p₁, p₂] path))) =
      ∫ omega, (if Manhattan.followPath omega 0 (List.ofFn path) = 0
        then (1 : ℂ) else 0) ∂Manhattan.environmentLaw := by
  letI : IsFiniteMeasure (volume.restrict Manhattan.Estimates.torus) := ⟨by
    rw [Measure.restrict_apply_univ, Manhattan.Estimates.torus]
    exact measure_Ioc_lt_top⟩
  let F : ℝ → ℝ → Manhattan.Environment → ℂ := fun p₁ p₂ omega =>
    sitePhase ![p₁, p₂] (Manhattan.followPath omega 0 (List.ofFn path))
  have hFmeas : Measurable fun q : (ℝ × ℝ) × Manhattan.Environment =>
      F q.1.1 q.1.2 q.2 := measurable_joint_pathPhase path
  have hslice (p₁ : ℝ) : Integrable
      (Function.uncurry fun p₂ omega => F p₁ p₂ omega)
      ((volume.restrict Manhattan.Estimates.torus).prod Manhattan.environmentLaw) := by
    apply Integrable.of_bound
      (hFmeas.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)).aestronglyMeasurable
      1
    filter_upwards with q
    exact le_of_eq (norm_joint_pathPhase path ((p₁, q.1), q.2))
  have hK : Integrable
      (Function.uncurry fun q : ℝ × Manhattan.Environment => fun p₂ : ℝ =>
        F q.1 p₂ q.2)
      (((volume.restrict Manhattan.Estimates.torus).prod Manhattan.environmentLaw).prod
        (volume.restrict Manhattan.Estimates.torus)) := by
    apply Integrable.of_bound
      (hFmeas.comp
        (((measurable_fst.comp measurable_fst).prodMk measurable_snd).prodMk
          (measurable_snd.comp measurable_fst))).aestronglyMeasurable
      1
    filter_upwards with q
    exact le_of_eq (norm_joint_pathPhase path ((q.1.1, q.2), q.1.2))
  have hraw : Integrable (fun q : ℝ × Manhattan.Environment =>
      ∫ p₂ in Manhattan.Estimates.torus, F q.1 p₂ q.2) <|
      (volume.restrict Manhattan.Estimates.torus).prod Manhattan.environmentLaw :=
    hK.integral_prod_left
  have hnormalized : Integrable (Function.uncurry fun p₁ omega =>
      Manhattan.Estimates.torusIntegral (fun p₂ => F p₁ p₂ omega))
      ((volume.restrict Manhattan.Estimates.torus).prod Manhattan.environmentLaw) := by
    simpa only [Manhattan.Estimates.torusIntegral, Complex.real_smul] using
      hraw.const_mul (((2 * Real.pi)⁻¹ : ℝ) : ℂ)
  simp_rw [inner_walshEmpty_pathVector]
  rw [show (fun p₁ : ℝ => Manhattan.Estimates.torusIntegral (fun p₂ : ℝ =>
      ∫ omega, F p₁ p₂ omega ∂Manhattan.environmentLaw)) =
      fun p₁ : ℝ => ∫ omega,
        Manhattan.Estimates.torusIntegral (fun p₂ : ℝ => F p₁ p₂ omega)
          ∂Manhattan.environmentLaw by
    funext p₁
    exact torusIntegral_integral_swap (fun p₂ omega => F p₁ p₂ omega) (hslice p₁)]
  rw [torusIntegral_integral_swap _ hnormalized]
  apply integral_congr_ae
  filter_upwards with omega
  simpa [F] using torusIntegral_sitePhase
    (Manhattan.followPath omega 0 (List.ofFn path))

private instance finite_torusMeasure :
    IsFiniteMeasure (volume.restrict Manhattan.Estimates.torus) := ⟨by
  rw [Measure.restrict_apply_univ, Manhattan.Estimates.torus]
  exact measure_Ioc_lt_top⟩

private theorem stronglyMeasurable_inner_pathVector_joint {n : ℕ}
    (path : Fin n → Manhattan.Axis) :
    StronglyMeasurable fun q : ℝ × ℝ =>
      inner ℂ (Manhattan.walshL2 ∅) (pathVector ![q.1, q.2] path) := by
  rw [show (fun q : ℝ × ℝ =>
      inner ℂ (Manhattan.walshL2 ∅) (pathVector ![q.1, q.2] path)) =
      fun q : ℝ × ℝ => ∫ omega, sitePhase ![q.1, q.2]
        (Manhattan.followPath omega 0 (List.ofFn path))
          ∂Manhattan.environmentLaw by
    funext q
    exact inner_walshEmpty_pathVector ![q.1, q.2] path]
  exact (measurable_joint_pathPhase path).stronglyMeasurable.integral_prod_right

private theorem norm_inner_pathVector_le_one {n : ℕ}
    (q : ℝ × ℝ) (path : Fin n → Manhattan.Axis) :
    ‖inner ℂ (Manhattan.walshL2 ∅) (pathVector ![q.1, q.2] path)‖ ≤ 1 := by
  rw [inner_walshEmpty_pathVector]
  refine (norm_integral_le_of_norm_le_const (C := 1) ?_).trans_eq ?_
  · filter_upwards with omega
    exact le_of_eq (norm_pathPhase ![q.1, q.2] (List.ofFn path) omega)
  · simp

private theorem integrable_inner_pathVector_joint {n : ℕ}
    (path : Fin n → Manhattan.Axis) :
    Integrable (fun q : ℝ × ℝ =>
      inner ℂ (Manhattan.walshL2 ∅) (pathVector ![q.1, q.2] path))
      ((volume.restrict Manhattan.Estimates.torus).prod
        (volume.restrict Manhattan.Estimates.torus)) := by
  apply Integrable.of_bound (stronglyMeasurable_inner_pathVector_joint path).aestronglyMeasurable 1
  filter_upwards with q
  exact norm_inner_pathVector_le_one q path

private theorem integrable_inner_pathVector_second {n : ℕ} (p₁ : ℝ)
    (path : Fin n → Manhattan.Axis) :
    Integrable (fun p₂ : ℝ =>
      inner ℂ (Manhattan.walshL2 ∅) (pathVector ![p₁, p₂] path))
      (volume.restrict Manhattan.Estimates.torus) := by
  apply Integrable.of_bound
    ((stronglyMeasurable_inner_pathVector_joint path).comp_measurable
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable 1
  filter_upwards with p₂
  exact norm_inner_pathVector_le_one (p₁, p₂) path

private theorem integrable_torusIntegral_inner_pathVector {n : ℕ}
    (path : Fin n → Manhattan.Axis) :
    Integrable (fun p₁ : ℝ => Manhattan.Estimates.torusIntegral (fun p₂ : ℝ =>
      inner ℂ (Manhattan.walshL2 ∅) (pathVector ![p₁, p₂] path)))
      (volume.restrict Manhattan.Estimates.torus) := by
  have h := (integrable_inner_pathVector_joint path).integral_prod_left
  simpa only [Manhattan.Estimates.torusIntegral, Complex.real_smul] using
    h.const_mul (((2 * Real.pi)⁻¹ : ℝ) : ℂ)

private theorem torusIntegral_finset_sum {ι : Type*} (s : Finset ι)
    (f : ι → ℝ → ℂ)
    (hf : ∀ i ∈ s, Integrable (f i) (volume.restrict Manhattan.Estimates.torus)) :
    Manhattan.Estimates.torusIntegral (fun p => ∑ i ∈ s, f i p) =
      ∑ i ∈ s, Manhattan.Estimates.torusIntegral (f i) := by
  simp only [Manhattan.Estimates.torusIntegral]
  rw [integral_finset_sum s hf, Finset.smul_sum]

private theorem stronglyMeasurable_inner_transition_pow (n : ℕ) :
    StronglyMeasurable fun q : ℝ × ℝ =>
      inner ℂ (Manhattan.walshL2 ∅)
        (((fiberTransition ![q.1, q.2]) ^ n) (Manhattan.walshL2 ∅)) := by
  rw [show (fun q : ℝ × ℝ =>
      inner ℂ (Manhattan.walshL2 ∅)
        (((fiberTransition ![q.1, q.2]) ^ n) (Manhattan.walshL2 ∅))) =
      fun q : ℝ × ℝ => ∑ path : Fin n → Manhattan.Axis,
        ∫ omega, sitePhase ![q.1, q.2]
          (Manhattan.followPath omega 0 (List.ofFn path))
            ∂Manhattan.environmentLaw by
    funext q
    rw [fiberTransition_pow_walsh]
    change (innerSL ℂ (Manhattan.walshL2 ∅))
      (∑ path : Fin n → Manhattan.Axis, pathVector ![q.1, q.2] path) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro path _
    exact inner_walshEmpty_pathVector ![q.1, q.2] path]
  apply Finset.stronglyMeasurable_fun_sum
  intro path _
  exact (measurable_joint_pathPhase path).stronglyMeasurable.integral_prod_right

private theorem norm_inner_transition_pow_le (q : ℝ × ℝ) (n : ℕ) :
    ‖inner ℂ (Manhattan.walshL2 ∅)
      (((fiberTransition ![q.1, q.2]) ^ n) (Manhattan.walshL2 ∅))‖ ≤ 4 ^ n := by
  have hu : ‖Manhattan.walshL2 ∅‖ = 1 := Manhattan.orthonormal_walshL2.1 ∅
  calc
    _ ≤ ‖Manhattan.walshL2 ∅‖ *
        ‖((fiberTransition ![q.1, q.2]) ^ n) (Manhattan.walshL2 ∅)‖ :=
      norm_inner_le_norm _ _
    _ ≤ 1 * (‖(fiberTransition ![q.1, q.2]) ^ n‖ * 1) := by
      rw [hu]
      gcongr
      simpa [hu] using ContinuousLinearMap.le_opNorm
        ((fiberTransition ![q.1, q.2]) ^ n) (Manhattan.walshL2 ∅)
    _ ≤ 4 ^ n := by
      rw [one_mul, mul_one]
      have hpow : ‖(fiberTransition ![q.1, q.2]) ^ n‖ ≤ 4 ^ n := by
        induction n with
        | zero =>
            change ‖ContinuousLinearMap.id ℂ Manhattan.WalshL2‖ ≤ 1
            apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
            intro x
            simp
        | succ n ih =>
            rw [pow_succ, pow_succ]
            exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
              (mul_le_mul ih (fiberTransition_norm_le_four _)
                (norm_nonneg _) (by positivity))
      exact hpow

private theorem torusIntegral₂_inner_transition_pow (n : ℕ) :
    Manhattan.Estimates.torusIntegral (fun p₁ : ℝ =>
      Manhattan.Estimates.torusIntegral (fun p₂ : ℝ =>
        inner ℂ (Manhattan.walshL2 ∅)
          (((fiberTransition ![p₁, p₂]) ^ n) (Manhattan.walshL2 ∅)))) =
      ∫ omega, ∑ path : Fin n → Manhattan.Axis,
        (if Manhattan.followPath omega 0 (List.ofFn path) = 0
          then (1 : ℂ) else 0) ∂Manhattan.environmentLaw := by
  simp_rw [fiberTransition_pow_walsh]
  change Manhattan.Estimates.torusIntegral (fun p₁ : ℝ =>
      Manhattan.Estimates.torusIntegral (fun p₂ : ℝ =>
        (innerSL ℂ (Manhattan.walshL2 ∅))
          (∑ path : Fin n → Manhattan.Axis, pathVector ![p₁, p₂] path))) = _
  simp_rw [map_sum]
  simp only [innerSL_apply_apply]
  rw [show (fun p₁ : ℝ => Manhattan.Estimates.torusIntegral (fun p₂ : ℝ =>
      ∑ path : Fin n → Manhattan.Axis,
        inner ℂ (Manhattan.walshL2 ∅) (pathVector ![p₁, p₂] path))) =
      fun p₁ : ℝ => ∑ path : Fin n → Manhattan.Axis,
        Manhattan.Estimates.torusIntegral (fun p₂ : ℝ =>
          inner ℂ (Manhattan.walshL2 ∅) (pathVector ![p₁, p₂] path)) by
    funext p₁
    exact torusIntegral_finset_sum Finset.univ _
      (fun path _ => integrable_inner_pathVector_second p₁ path)]
  rw [show Manhattan.Estimates.torusIntegral (fun p₁ : ℝ =>
      ∑ path : Fin n → Manhattan.Axis,
        Manhattan.Estimates.torusIntegral (fun p₂ : ℝ =>
          inner ℂ (Manhattan.walshL2 ∅) (pathVector ![p₁, p₂] path))) =
      ∑ path : Fin n → Manhattan.Axis,
        Manhattan.Estimates.torusIntegral (fun p₁ : ℝ =>
          Manhattan.Estimates.torusIntegral (fun p₂ : ℝ =>
            inner ℂ (Manhattan.walshL2 ∅) (pathVector ![p₁, p₂] path))) by
    exact torusIntegral_finset_sum Finset.univ _
      (fun path _ => integrable_torusIntegral_inner_pathVector path)]
  simp_rw [torusIntegral_inner_pathVector]
  rw [integral_finset_sum]
  intro path _
  apply Integrable.of_bound
    (Measurable.ite
      ((measurableSet_singleton (0 : Manhattan.Site)).preimage
        (Manhattan.measurable_followPath 0 (List.ofFn path)))
      measurable_const measurable_const).aestronglyMeasurable 1
  filter_upwards with omega
  split <;> simp

private theorem torusIntegral₂_eq_prodIntegral
    (f : ℝ → ℝ → ℂ)
    (hf : Integrable (Function.uncurry f)
      ((volume.restrict Manhattan.Estimates.torus).prod
        (volume.restrict Manhattan.Estimates.torus))) :
    Manhattan.Estimates.torusIntegral (fun p₁ : ℝ =>
      Manhattan.Estimates.torusIntegral (fun p₂ : ℝ => f p₁ p₂)) =
      ((2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹ : ℝ) •
        ∫ q : ℝ × ℝ, f q.1 q.2
          ∂((volume.restrict Manhattan.Estimates.torus).prod
            (volume.restrict Manhattan.Estimates.torus)) := by
  simp only [Manhattan.Estimates.torusIntegral]
  rw [← integral_smul]
  simp only [smul_smul]
  rw [integral_smul]
  rw [integral_integral hf]

private theorem torusIntegral₂_real_eq_prodIntegral
    (f : ℝ → ℝ → ℝ)
    (hf : Integrable (Function.uncurry f)
      ((volume.restrict Manhattan.Estimates.torus).prod
        (volume.restrict Manhattan.Estimates.torus))) :
    Manhattan.Estimates.torusIntegral (fun p₁ : ℝ =>
      Manhattan.Estimates.torusIntegral (fun p₂ : ℝ => f p₁ p₂)) =
      ((2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹ : ℝ) *
        ∫ q : ℝ × ℝ, f q.1 q.2
          ∂((volume.restrict Manhattan.Estimates.torus).prod
            (volume.restrict Manhattan.Estimates.torus)) := by
  simp only [Manhattan.Estimates.torusIntegral, smul_eq_mul]
  rw [integral_const_mul]
  rw [integral_integral hf]
  ring

private theorem torusIntegral₂_inner_semigroup_eq_tsum (t : ℝ) (ht : 0 ≤ t) :
    Manhattan.Estimates.torusIntegral (fun p₁ : ℝ =>
      Manhattan.Estimates.torusIntegral (fun p₂ : ℝ =>
        inner ℂ (Manhattan.walshL2 ∅)
          (Manhattan.Operator.operatorSemigroup
            (Manhattan.concreteFiberEnvironment.fiberGenerator ![p₁, p₂]) t
            (Manhattan.walshL2 ∅)))) =
      ∑' n : ℕ, (Real.exp (-2 * t) * t ^ n / n.factorial : ℝ) •
        (∫ omega, ∑ path : Fin n → Manhattan.Axis,
          (if Manhattan.followPath omega 0 (List.ofFn path) = 0
            then (1 : ℂ) else 0) ∂Manhattan.environmentLaw) := by
  let c : ℕ → ℝ := fun n => Real.exp (-2 * t) * t ^ n / n.factorial
  let B : ℕ → ℝ := fun n => c n * 4 ^ n
  let F : ℕ → (ℝ × ℝ) → ℂ := fun n q =>
    (c n : ℂ) * inner ℂ (Manhattan.walshL2 ∅)
      (((fiberTransition ![q.1, q.2]) ^ n) (Manhattan.walshL2 ∅))
  have hc (n : ℕ) : 0 ≤ c n := by
    dsimp [c]
    positivity
  have hB_nonneg (n : ℕ) : 0 ≤ B n := mul_nonneg (hc n) (by positivity)
  have hB : Summable B := by
    have h := (Real.summable_pow_div_factorial (4 * t)).mul_left (Real.exp (-2 * t))
    refine h.congr fun n => ?_
    dsimp [B, c]
    rw [mul_pow, div_eq_mul_inv]
    ring
  have hF_bound (n : ℕ) (q : ℝ × ℝ) : ‖F n q‖ ≤ B n := by
    dsimp [F, B]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hc n)]
    exact mul_le_mul_of_nonneg_left (norm_inner_transition_pow_le q n) (hc n)
  have hF_int (n : ℕ) : Integrable (F n)
      ((volume.restrict Manhattan.Estimates.torus).prod
        (volume.restrict Manhattan.Estimates.torus)) := by
    apply Integrable.of_bound
      ((stronglyMeasurable_inner_transition_pow n).const_mul (c n : ℂ)).aestronglyMeasurable
      (B n)
    filter_upwards with q
    exact hF_bound n q
  let μ₂ := (volume.restrict Manhattan.Estimates.torus).prod
    (volume.restrict Manhattan.Estimates.torus)
  have hnormIntegral (n : ℕ) :
      (∫ q : ℝ × ℝ, ‖F n q‖ ∂μ₂) ≤ B n * μ₂.real Set.univ := by
    rw [show μ₂ = (volume.restrict Manhattan.Estimates.torus).prod
      (volume.restrict Manhattan.Estimates.torus) by rfl]
    calc
      _ ≤ ∫ _q : ℝ × ℝ, B n ∂((volume.restrict Manhattan.Estimates.torus).prod
          (volume.restrict Manhattan.Estimates.torus)) := by
        apply integral_mono_ae (hF_int n).norm (integrable_const (B n))
        filter_upwards with q
        exact hF_bound n q
      _ = ((volume.restrict Manhattan.Estimates.torus).prod
          (volume.restrict Manhattan.Estimates.torus)).real Set.univ * B n :=
        integral_const (B n)
      _ = _ := mul_comm _ _
  have hnormSummable : Summable fun n : ℕ => ∫ q : ℝ × ℝ, ‖F n q‖ ∂μ₂ := by
    apply Summable.of_nonneg_of_le
      (fun n => integral_nonneg fun q => norm_nonneg (F n q)) hnormIntegral
    exact hB.mul_right (μ₂.real Set.univ)
  have hF_point (q : ℝ × ℝ) : Summable fun n => F n q :=
    hB.of_norm_bounded fun n => hF_bound n q
  have hFsum_strong : StronglyMeasurable fun q : ℝ × ℝ => ∑' n, F n q := by
    apply stronglyMeasurable_of_tendsto (Filter.atTop : Filter ℕ)
    · intro N
      exact Finset.stronglyMeasurable_fun_sum (Finset.range N) fun n _ =>
        (stronglyMeasurable_inner_transition_pow n).const_mul (c n : ℂ)
    · rw [tendsto_pi_nhds]
      intro q
      exact (hF_point q).hasSum.tendsto_sum_nat
  have hFsum_int : Integrable (fun q : ℝ × ℝ => ∑' n, F n q) μ₂ := by
    apply Integrable.of_bound hFsum_strong.aestronglyMeasurable (∑' n, B n)
    filter_upwards with q
    exact (norm_tsum_le_tsum_norm (hF_point q).norm).trans
      ((hF_point q).norm.tsum_le_tsum (fun n => hF_bound n q) hB)
  have hIntegralSummable : Summable fun n : ℕ => ∫ q : ℝ × ℝ, F n q ∂μ₂ :=
    hnormSummable.of_norm_bounded fun n => norm_integral_le_integral_norm _
  have hswap : (∑' n : ℕ, ∫ q : ℝ × ℝ, F n q ∂μ₂) =
      ∫ q : ℝ × ℝ, ∑' n, F n q ∂μ₂ :=
    integral_tsum_of_summable_integral_norm hF_int hnormSummable
  have hpoint (p₁ p₂ : ℝ) :
      inner ℂ (Manhattan.walshL2 ∅)
          (Manhattan.Operator.operatorSemigroup
            (Manhattan.concreteFiberEnvironment.fiberGenerator ![p₁, p₂]) t
            (Manhattan.walshL2 ∅)) =
        ∑' n, F n (p₁, p₂) := by
    rw [inner_walshEmpty_semigroup_eq_tsum]
    apply tsum_congr
    intro n
    simp only [F, c, RCLike.real_smul_eq_coe_smul (K := ℂ),
      smul_eq_mul]
    rfl
  calc
    _ = Manhattan.Estimates.torusIntegral (fun p₁ : ℝ =>
        Manhattan.Estimates.torusIntegral (fun p₂ : ℝ =>
          ∑' n, F n (p₁, p₂))) := by
      congr 1
      funext p₁
      congr 1
      funext p₂
      exact hpoint p₁ p₂
    _ = ((2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹ : ℝ) •
        ∫ q : ℝ × ℝ, ∑' n, F n q ∂μ₂ := by
      apply torusIntegral₂_eq_prodIntegral
      simpa only [μ₂] using hFsum_int
    _ = ((2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹ : ℝ) •
        ∑' n : ℕ, ∫ q : ℝ × ℝ, F n q ∂μ₂ := by rw [← hswap]
    _ = ∑' n : ℕ, ((2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹ : ℝ) •
        ∫ q : ℝ × ℝ, F n q ∂μ₂ := by
      rw [hIntegralSummable.tsum_const_smul]
    _ = ∑' n : ℕ, Manhattan.Estimates.torusIntegral (fun p₁ : ℝ =>
        Manhattan.Estimates.torusIntegral (fun p₂ : ℝ => F n (p₁, p₂))) := by
      apply tsum_congr
      intro n
      symm
      apply torusIntegral₂_eq_prodIntegral
      simpa only [μ₂] using hF_int n
    _ = _ := by
      apply tsum_congr
      intro n
      rw [show (fun p₁ : ℝ => Manhattan.Estimates.torusIntegral (fun p₂ : ℝ =>
          F n (p₁, p₂))) = fun p₁ : ℝ =>
          (c n : ℂ) * Manhattan.Estimates.torusIntegral (fun p₂ : ℝ =>
            inner ℂ (Manhattan.walshL2 ∅)
              (((fiberTransition ![p₁, p₂]) ^ n) (Manhattan.walshL2 ∅))) by
        funext p₁
        exact torusIntegral_const_mul _ _]
      rw [torusIntegral_const_mul, torusIntegral₂_inner_transition_pow]
      simp only [c, RCLike.real_smul_eq_coe_smul (K := ℂ), smul_eq_mul]
      rfl

private theorem torusIntegral₂_inner_semigroup_eq_annealed (t : ℝ) (ht : 0 ≤ t) :
    Manhattan.Estimates.torusIntegral (fun p₁ : ℝ =>
      Manhattan.Estimates.torusIntegral (fun p₂ : ℝ =>
        inner ℂ (Manhattan.walshL2 ∅)
          (Manhattan.Operator.operatorSemigroup
            (Manhattan.concreteFiberEnvironment.fiberGenerator ![p₁, p₂]) t
            (Manhattan.walshL2 ∅)))) =
      (Manhattan.annealedContinuousKernel t 0 0).toReal := by
  let a : ℕ → ℝ := fun n =>
    (Real.exp (-2 * t) * t ^ n / n.factorial) *
      ∫ omega, pathReturnCount n omega ∂Manhattan.environmentLaw
  have ha_nonneg (n : ℕ) : 0 ≤ a n := by
    dsimp [a]
    exact mul_nonneg
      (div_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg ht n)) (Nat.cast_nonneg _))
      (integral_pathReturnCount_nonneg n)
  have hkernel := congrArg ENNReal.toReal
    (annealedContinuousKernel_eq_ofReal_tsum t ht)
  rw [ENNReal.toReal_ofReal (tsum_nonneg ha_nonneg)] at hkernel
  rw [torusIntegral₂_inner_semigroup_eq_tsum t ht]
  simp_rw [integral_complex_pathReturnCount]
  calc
    (∑' n : ℕ, (Real.exp (-2 * t) * t ^ n / n.factorial : ℝ) •
        ((∫ omega, pathReturnCount n omega ∂Manhattan.environmentLaw : ℝ) : ℂ)) =
        ∑' n, ((a n : ℝ) : ℂ) := by
      apply tsum_congr
      intro n
      simp [a, RCLike.real_smul_eq_coe_smul (K := ℂ), smul_eq_mul]
    _ = ((∑' n, a n : ℝ) : ℂ) := (Complex.ofReal_tsum a).symm
    _ = ((Manhattan.annealedContinuousKernel t 0 0).toReal : ℂ) :=
      congrArg (fun x : ℝ => (x : ℂ)) hkernel.symm

private theorem concrete_minus_eq_resolventOperator (p : Fin 2 → ℝ) (lambda : ℝ) :
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).minus lambda =
      Manhattan.Operator.resolventOperator
        (Manhattan.concreteFiberEnvironment.fiberGenerator p) lambda := by
  change (((lambda : ℂ) • ContinuousLinearMap.id ℂ Manhattan.WalshL2 -
      Manhattan.concreteFiberEnvironment.fiberS p) -
        Manhattan.concreteFiberEnvironment.fiberA p) =
    (lambda : ℂ) • ContinuousLinearMap.id ℂ Manhattan.WalshL2 -
      (Manhattan.concreteFiberEnvironment.fiberS p +
        Manhattan.concreteFiberEnvironment.fiberA p)
  abel

private theorem concrete_resolventQuadratic_eq_re_integral
    (p : Fin 2 → ℝ) (lambda : ℝ) (hlambda : 0 < lambda) :
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).resolventQuadratic
        hlambda (Manhattan.walshL2 ∅) =
      re (∫ t in Ioi 0, Manhattan.Operator.semigroupCorrelation
        (Manhattan.concreteFiberEnvironment.fiberGenerator p) lambda
        (Manhattan.walshL2 ∅) t) := by
  let P := Manhattan.concreteFiberEnvironment.dissipativeSkewPair p
  let G := Manhattan.concreteFiberEnvironment.fiberGenerator p
  have hinverse : (P.minusEquiv hlambda).symm (Manhattan.walshL2 ∅) =
      (Manhattan.Operator.resolventEquiv G hlambda
        (concreteFiberSemigroup_contract p)).symm (Manhattan.walshL2 ∅) := by
    apply (P.minus_bijective hlambda).1
    rw [P.minus_apply_inverse]
    rw [show P.minus lambda = Manhattan.Operator.resolventOperator G lambda by
      exact concrete_minus_eq_resolventOperator p lambda]
    exact (Manhattan.Operator.resolventEquiv G hlambda
      (concreteFiberSemigroup_contract p)).apply_symm_apply (Manhattan.walshL2 ∅) |>.symm
  rw [Manhattan.Operator.DissipativeSkewPair.resolventQuadratic, hinverse,
    ← Manhattan.Operator.integral_inner_operatorSemigroup_eq_resolvent G hlambda
      (Manhattan.walshL2 ∅) (concreteFiberSemigroup_contract p)]

private theorem stronglyMeasurable_joint_inner_semigroup :
    StronglyMeasurable fun q : (ℝ × ℝ) × ℝ =>
      inner ℂ (Manhattan.walshL2 ∅)
        (Manhattan.Operator.operatorSemigroup
          (Manhattan.concreteFiberEnvironment.fiberGenerator ![q.1.1, q.1.2]) q.2
          (Manhattan.walshL2 ∅)) := by
  let F : ℕ → ((ℝ × ℝ) × ℝ) → ℂ := fun n q =>
    (Real.exp (-2 * q.2) * q.2 ^ n / n.factorial : ℝ) *
      inner ℂ (Manhattan.walshL2 ∅)
        (((fiberTransition ![q.1.1, q.1.2]) ^ n) (Manhattan.walshL2 ∅))
  have hF (n : ℕ) : StronglyMeasurable (F n) := by
    apply StronglyMeasurable.mul
    · exact (show Continuous fun q : (ℝ × ℝ) × ℝ =>
          ((Real.exp (-2 * q.2) * q.2 ^ n / n.factorial : ℝ) : ℂ) by
        fun_prop).stronglyMeasurable
    · exact (stronglyMeasurable_inner_transition_pow n).comp_measurable measurable_fst
  have hsum (q : (ℝ × ℝ) × ℝ) : Summable fun n => F n q := by
    let L := innerSL ℂ (Manhattan.walshL2 ∅)
    have h := (summable_concreteFiberSemigroup_series ![q.1.1, q.1.2] q.2
      (Manhattan.walshL2 ∅)).map L L.continuous
    refine h.congr fun n => ?_
    simp only [Function.comp_apply, F, L, innerSL_apply_apply, inner_smul_right,
      RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rfl
  have hlimit : StronglyMeasurable fun q : (ℝ × ℝ) × ℝ => ∑' n, F n q := by
    apply stronglyMeasurable_of_tendsto (Filter.atTop : Filter ℕ)
    · intro N
      exact Finset.stronglyMeasurable_fun_sum (Finset.range N) fun n _ => hF n
    · rw [tendsto_pi_nhds]
      intro q
      exact (hsum q).hasSum.tendsto_sum_nat
  rw [show (fun q : (ℝ × ℝ) × ℝ =>
      inner ℂ (Manhattan.walshL2 ∅)
        (Manhattan.Operator.operatorSemigroup
          (Manhattan.concreteFiberEnvironment.fiberGenerator ![q.1.1, q.1.2]) q.2
          (Manhattan.walshL2 ∅))) = fun q => ∑' n, F n q by
    funext q
    rw [inner_walshEmpty_semigroup_eq_tsum]
    apply tsum_congr
    intro n
    simp only [F, RCLike.real_smul_eq_coe_smul (K := ℂ), smul_eq_mul]
    rfl]
  exact hlimit

private theorem norm_inner_concreteFiberSemigroup_le_one
    (p : Fin 2 → ℝ) (t : ℝ) (ht : 0 ≤ t) :
    ‖inner ℂ (Manhattan.walshL2 ∅)
      (Manhattan.Operator.operatorSemigroup
        (Manhattan.concreteFiberEnvironment.fiberGenerator p) t
        (Manhattan.walshL2 ∅))‖ ≤ 1 := by
  have hu : ‖Manhattan.walshL2 ∅‖ = 1 := Manhattan.orthonormal_walshL2.1 ∅
  calc
    _ ≤ ‖Manhattan.walshL2 ∅‖ *
        ‖Manhattan.Operator.operatorSemigroup
          (Manhattan.concreteFiberEnvironment.fiberGenerator p) t
          (Manhattan.walshL2 ∅)‖ := norm_inner_le_norm _ _
    _ ≤ 1 * (‖Manhattan.Operator.operatorSemigroup
          (Manhattan.concreteFiberEnvironment.fiberGenerator p) t‖ * 1) := by
      rw [hu]
      gcongr
      simpa only [hu] using ContinuousLinearMap.le_opNorm
        (Manhattan.Operator.operatorSemigroup
          (Manhattan.concreteFiberEnvironment.fiberGenerator p) t)
        (Manhattan.walshL2 ∅)
    _ ≤ 1 := by
      simpa using concreteFiberSemigroup_contract p t ht

private theorem stronglyMeasurable_joint_semigroupCorrelation (lambda : ℝ) :
    StronglyMeasurable fun q : (ℝ × ℝ) × ℝ =>
      Manhattan.Operator.semigroupCorrelation
        (Manhattan.concreteFiberEnvironment.fiberGenerator ![q.1.1, q.1.2]) lambda
        (Manhattan.walshL2 ∅) q.2 := by
  rw [show (fun q : (ℝ × ℝ) × ℝ =>
      Manhattan.Operator.semigroupCorrelation
        (Manhattan.concreteFiberEnvironment.fiberGenerator ![q.1.1, q.1.2]) lambda
        (Manhattan.walshL2 ∅) q.2) = fun q =>
      ((Real.exp (-lambda * q.2) : ℝ) : ℂ) *
        inner ℂ (Manhattan.walshL2 ∅)
          (Manhattan.Operator.operatorSemigroup
            (Manhattan.concreteFiberEnvironment.fiberGenerator ![q.1.1, q.1.2]) q.2
            (Manhattan.walshL2 ∅)) by
    funext q
    rfl]
  exact (show Continuous fun q : (ℝ × ℝ) × ℝ =>
      ((Real.exp (-lambda * q.2) : ℝ) : ℂ) by
    fun_prop).stronglyMeasurable.mul stronglyMeasurable_joint_inner_semigroup

private theorem integrable_joint_semigroupCorrelation
    (lambda : ℝ) (hlambda : 0 < lambda) :
    Integrable (fun q : (ℝ × ℝ) × ℝ =>
      Manhattan.Operator.semigroupCorrelation
        (Manhattan.concreteFiberEnvironment.fiberGenerator ![q.1.1, q.1.2]) lambda
        (Manhattan.walshL2 ∅) q.2)
      (((volume.restrict Manhattan.Estimates.torus).prod
        (volume.restrict Manhattan.Estimates.torus)).prod
          (volume.restrict (Ioi 0))) := by
  let μ₂ := (volume.restrict Manhattan.Estimates.torus).prod
    (volume.restrict Manhattan.Estimates.torus)
  have htime : Integrable (fun t : ℝ => Real.exp (-lambda * t))
      (volume.restrict (Ioi 0)) :=
    integrableOn_exp_mul_Ioi (a := -lambda) (by linarith) 0
  have hdom : Integrable (fun q : (ℝ × ℝ) × ℝ =>
      (1 : ℝ) * Real.exp (-lambda * q.2))
      (μ₂.prod (volume.restrict (Ioi 0))) :=
    (integrable_const (1 : ℝ)).mul_prod htime
  apply Integrable.mono' hdom
  · simpa only [μ₂] using
      (stronglyMeasurable_joint_semigroupCorrelation lambda).aestronglyMeasurable
  · rw [Measure.ae_prod_iff_ae_ae (measurableSet_le
        (stronglyMeasurable_joint_semigroupCorrelation lambda).measurable.norm
        (by fun_prop))]
    filter_upwards with p
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp only [one_mul, Manhattan.Operator.semigroupCorrelation, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (norm_inner_concreteFiberSemigroup_le_one ![p.1, p.2] t ht.le)
      (Real.exp_pos (-lambda * t)).le

private theorem integrable_torus_inner_semigroup (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun p : ℝ × ℝ =>
      inner ℂ (Manhattan.walshL2 ∅)
        (Manhattan.Operator.operatorSemigroup
          (Manhattan.concreteFiberEnvironment.fiberGenerator ![p.1, p.2]) t
          (Manhattan.walshL2 ∅)))
      ((volume.restrict Manhattan.Estimates.torus).prod
        (volume.restrict Manhattan.Estimates.torus)) := by
  apply Integrable.of_bound
    ((stronglyMeasurable_joint_inner_semigroup.comp_measurable
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable) 1
  filter_upwards with p
  exact norm_inner_concreteFiberSemigroup_le_one ![p.1, p.2] t ht

private theorem integrable_torus_resolventQuadratic
    (lambda : ℝ) (hlambda : 0 < lambda) :
    Integrable (fun p : ℝ × ℝ =>
      (Manhattan.concreteFiberEnvironment.dissipativeSkewPair ![p.1, p.2]).resolventQuadratic
        hlambda (Manhattan.walshL2 ∅))
      ((volume.restrict Manhattan.Estimates.torus).prod
        (volume.restrict Manhattan.Estimates.torus)) := by
  have h := (integrable_joint_semigroupCorrelation lambda hlambda).integral_prod_left.re
  refine h.congr ?_
  filter_upwards with p
  exact (concrete_resolventQuadratic_eq_re_integral ![p.1, p.2] lambda hlambda).symm

private theorem normalized_prodIntegral_semigroupCorrelation_eq
    (lambda t : ℝ) (ht : 0 ≤ t) :
    ((2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹ : ℝ) *
        re (∫ p : ℝ × ℝ, Manhattan.Operator.semigroupCorrelation
          (Manhattan.concreteFiberEnvironment.fiberGenerator ![p.1, p.2]) lambda
          (Manhattan.walshL2 ∅) t
          ∂((volume.restrict Manhattan.Estimates.torus).prod
            (volume.restrict Manhattan.Estimates.torus))) =
      Real.exp (-lambda * t) *
        (Manhattan.annealedContinuousKernel t 0 0).toReal := by
  let μ₂ := (volume.restrict Manhattan.Estimates.torus).prod
    (volume.restrict Manhattan.Estimates.torus)
  let k : ℝ := (2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹
  let innerFiber : (ℝ × ℝ) → ℂ := fun p =>
    inner ℂ (Manhattan.walshL2 ∅)
      (Manhattan.Operator.operatorSemigroup
        (Manhattan.concreteFiberEnvironment.fiberGenerator ![p.1, p.2]) t
        (Manhattan.walshL2 ∅))
  have hinner : Integrable innerFiber μ₂ := by
    simpa only [innerFiber, μ₂] using integrable_torus_inner_semigroup t ht
  have hcorrelation :
      (∫ p : ℝ × ℝ, Manhattan.Operator.semigroupCorrelation
          (Manhattan.concreteFiberEnvironment.fiberGenerator ![p.1, p.2]) lambda
          (Manhattan.walshL2 ∅) t ∂μ₂) =
        (Real.exp (-lambda * t) : ℂ) * ∫ p, innerFiber p ∂μ₂ := by
    rw [show (fun p : ℝ × ℝ => Manhattan.Operator.semigroupCorrelation
        (Manhattan.concreteFiberEnvironment.fiberGenerator ![p.1, p.2]) lambda
        (Manhattan.walshL2 ∅) t) = fun p =>
          (Real.exp (-lambda * t) : ℂ) * innerFiber p by
      funext p
      rfl]
    exact integral_const_mul _ _
  have hnormalized :
      (k : ℂ) * ∫ p, innerFiber p ∂μ₂ =
        ((Manhattan.annealedContinuousKernel t 0 0).toReal : ℂ) := by
    have hprod := torusIntegral₂_eq_prodIntegral
      (fun p₁ p₂ => innerFiber (p₁, p₂)) (by
        simpa only [innerFiber, μ₂] using hinner)
    calc
      _ = Manhattan.Estimates.torusIntegral (fun p₁ : ℝ =>
          Manhattan.Estimates.torusIntegral (fun p₂ : ℝ => innerFiber (p₁, p₂))) := by
        simpa only [k, μ₂, RCLike.real_smul_eq_coe_smul (K := ℂ)] using hprod.symm
      _ = _ := by
        simpa only [innerFiber] using torusIntegral₂_inner_semigroup_eq_annealed t ht
  have hcomplex :
      (k : ℂ) *
          (∫ p : ℝ × ℝ, Manhattan.Operator.semigroupCorrelation
            (Manhattan.concreteFiberEnvironment.fiberGenerator ![p.1, p.2]) lambda
            (Manhattan.walshL2 ∅) t ∂μ₂) =
        (Real.exp (-lambda * t) : ℂ) *
          ((Manhattan.annealedContinuousKernel t 0 0).toReal : ℂ) := by
    rw [hcorrelation]
    calc
      (k : ℂ) * ((Real.exp (-lambda * t) : ℂ) * ∫ p, innerFiber p ∂μ₂) =
          (Real.exp (-lambda * t) : ℂ) *
            ((k : ℂ) * ∫ p, innerFiber p ∂μ₂) := by ring
      _ = _ := by rw [hnormalized]
  have hcomplex' :
      k • (∫ p : ℝ × ℝ, Manhattan.Operator.semigroupCorrelation
          (Manhattan.concreteFiberEnvironment.fiberGenerator ![p.1, p.2]) lambda
          (Manhattan.walshL2 ∅) t ∂μ₂) =
        Real.exp (-lambda * t) •
          ((Manhattan.annealedContinuousKernel t 0 0).toReal : ℂ) := by
    simpa only [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_eq_mul] using hcomplex
  have hre := congrArg (RCLike.reCLM : ℂ →L[ℝ] ℝ) hcomplex'
  simpa only [k, μ₂, ContinuousLinearMap.map_smul, RCLike.reCLM_apply,
    Complex.ofReal_re, smul_eq_mul] using hre

private theorem concrete_green_identity_real (lambda : ℝ) (hlambda : 0 < lambda) :
    (∫ t in Ioi 0, Real.exp (-lambda * t) *
        (Manhattan.annealedContinuousKernel t 0 0).toReal) =
      Manhattan.Estimates.torusIntegral (fun p₁ : ℝ =>
        Manhattan.Estimates.torusIntegral (fun p₂ : ℝ =>
          (Manhattan.concreteFiberEnvironment.dissipativeSkewPair ![p₁, p₂]).resolventQuadratic
            hlambda (Manhattan.walshL2 ∅))) := by
  let μ₂ := (volume.restrict Manhattan.Estimates.torus).prod
    (volume.restrict Manhattan.Estimates.torus)
  let k : ℝ := (2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹
  let correlation : (ℝ × ℝ) → ℝ → ℂ := fun p t =>
    Manhattan.Operator.semigroupCorrelation
      (Manhattan.concreteFiberEnvironment.fiberGenerator ![p.1, p.2]) lambda
      (Manhattan.walshL2 ∅) t
  have hjoint : Integrable (Function.uncurry correlation)
      (μ₂.prod (volume.restrict (Ioi 0))) := by
    simpa only [correlation, μ₂, Function.uncurry_apply_pair] using
      integrable_joint_semigroupCorrelation lambda hlambda
  have hleft := hjoint.integral_prod_left
  have hright := hjoint.integral_prod_right
  symm
  calc
    Manhattan.Estimates.torusIntegral (fun p₁ : ℝ =>
        Manhattan.Estimates.torusIntegral (fun p₂ : ℝ =>
          (Manhattan.concreteFiberEnvironment.dissipativeSkewPair ![p₁, p₂]).resolventQuadratic
            hlambda (Manhattan.walshL2 ∅))) =
        k * ∫ p : ℝ × ℝ,
          (Manhattan.concreteFiberEnvironment.dissipativeSkewPair ![p.1, p.2]).resolventQuadratic
            hlambda (Manhattan.walshL2 ∅) ∂μ₂ := by
      apply torusIntegral₂_real_eq_prodIntegral
      simpa only [μ₂] using integrable_torus_resolventQuadratic lambda hlambda
    _ = k * ∫ p : ℝ × ℝ, re (∫ t in Ioi 0, correlation p t) ∂μ₂ := by
      congr 1
      apply integral_congr_ae
      filter_upwards with p
      exact concrete_resolventQuadratic_eq_re_integral ![p.1, p.2] lambda hlambda
    _ = k * re (∫ p : ℝ × ℝ, (∫ t in Ioi 0, correlation p t) ∂μ₂) := by
      have hl : Integrable (fun p => ∫ t in Ioi 0, correlation p t) μ₂ := by
        simpa only [Function.uncurry_apply_pair] using hleft
      rw [integral_re hl]
    _ = k * re (∫ t in Ioi 0, ∫ p : ℝ × ℝ, correlation p t ∂μ₂) := by
      rw [integral_integral_swap hjoint]
    _ = k * ∫ t in Ioi 0, re (∫ p : ℝ × ℝ, correlation p t ∂μ₂) := by
      have hr : Integrable (fun t => ∫ p : ℝ × ℝ, correlation p t ∂μ₂)
          (volume.restrict (Ioi 0)) := by
        simpa only [Function.uncurry_apply_pair] using hright
      rw [integral_re hr]
    _ = ∫ t in Ioi 0, k * re (∫ p : ℝ × ℝ, correlation p t ∂μ₂) := by
      rw [integral_const_mul]
    _ = ∫ t in Ioi 0, Real.exp (-lambda * t) *
        (Manhattan.annealedContinuousKernel t 0 0).toReal := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      simpa only [k, μ₂, correlation] using
        normalized_prodIntegral_semigroupCorrelation_eq lambda t ht.le

private theorem annealedContinuousKernel_ne_top (t : ℝ) (ht : 0 ≤ t) :
    Manhattan.annealedContinuousKernel t 0 0 ≠ ∞ := by
  rw [annealedContinuousKernel_eq_ofReal_tsum t ht]
  exact ENNReal.ofReal_ne_top

private theorem integrable_annealed_damped (lambda : ℝ) (hlambda : 0 < lambda) :
    Integrable (fun t => Real.exp (-lambda * t) *
      (Manhattan.annealedContinuousKernel t 0 0).toReal)
      (volume.restrict (Ioi 0)) := by
  let μ₂ := (volume.restrict Manhattan.Estimates.torus).prod
    (volume.restrict Manhattan.Estimates.torus)
  let k : ℝ := (2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹
  let correlation : (ℝ × ℝ) → ℝ → ℂ := fun p t =>
    Manhattan.Operator.semigroupCorrelation
      (Manhattan.concreteFiberEnvironment.fiberGenerator ![p.1, p.2]) lambda
      (Manhattan.walshL2 ∅) t
  have hjoint : Integrable (Function.uncurry correlation)
      (μ₂.prod (volume.restrict (Ioi 0))) := by
    simpa only [correlation, μ₂, Function.uncurry_apply_pair] using
      integrable_joint_semigroupCorrelation lambda hlambda
  have hright : Integrable (fun t => ∫ p : ℝ × ℝ, correlation p t ∂μ₂)
      (volume.restrict (Ioi 0)) := by
    simpa only [Function.uncurry_apply_pair] using hjoint.integral_prod_right
  have hnormalized : Integrable (fun t =>
      k * re (∫ p : ℝ × ℝ, correlation p t ∂μ₂))
      (volume.restrict (Ioi 0)) := hright.re.const_mul k
  refine hnormalized.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simpa only [k, μ₂, correlation] using
    normalized_prodIntegral_semigroupCorrelation_eq lambda t ht.le

private theorem concrete_green_identity (lambda : ℝ) (hlambda : 0 < lambda) :
    (∫⁻ t in Ici 0,
      ENNReal.ofReal (Real.exp (-lambda * t)) *
        Manhattan.annealedContinuousKernel t 0 0) =
      ENNReal.ofReal
        (Manhattan.Estimates.torusIntegral fun p₁ : ℝ =>
          Manhattan.Estimates.torusIntegral fun p₂ : ℝ =>
            (Manhattan.concreteFiberEnvironment.dissipativeSkewPair ![p₁, p₂]).resolventQuadratic
              hlambda (Manhattan.walshL2 ∅)) := by
  rw [← restrict_Ioi_eq_restrict_Ici]
  calc
    (∫⁻ t in Ioi 0, ENNReal.ofReal (Real.exp (-lambda * t)) *
        Manhattan.annealedContinuousKernel t 0 0) =
        ∫⁻ t in Ioi 0, ENNReal.ofReal (Real.exp (-lambda * t) *
          (Manhattan.annealedContinuousKernel t 0 0).toReal) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      calc
        ENNReal.ofReal (Real.exp (-lambda * t)) *
            Manhattan.annealedContinuousKernel t 0 0 =
          ENNReal.ofReal (Real.exp (-lambda * t)) *
            ENNReal.ofReal (Manhattan.annealedContinuousKernel t 0 0).toReal := by
              rw [ENNReal.ofReal_toReal (annealedContinuousKernel_ne_top t ht.le)]
        _ = _ := (ENNReal.ofReal_mul (Real.exp_pos _).le).symm
    _ = ENNReal.ofReal (∫ t in Ioi 0, Real.exp (-lambda * t) *
        (Manhattan.annealedContinuousKernel t 0 0).toReal) := by
      symm
      exact ofReal_integral_eq_lintegral_ofReal (integrable_annealed_damped lambda hlambda)
        (Filter.Eventually.of_forall fun t =>
          mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg)
    _ = _ := congrArg ENNReal.ofReal (concrete_green_identity_real lambda hlambda)

/-- Concrete Proposition 2.1: the fair-coin Walsh fiber has generator
`G_p=S_p+A_p`, and its averaged resolvent is the Laplace transform of the
annealed return kernel. Paper: `manuscript.tex:576-607`. -/
theorem proposition_generator :
    ∃ D : Manhattan.Operator.FiberEnvironment Manhattan.WalshL2,
      D.shift = Manhattan.environmentShift ∧
      D.omega = Manhattan.originSignMultiplier ∧
      (∀ p : Fin 2 → ℝ, D.fiberGenerator p = D.fiberS p + D.fiberA p) ∧
      ∀ (lambda : ℝ), ∀ hlambda : 0 < lambda,
        (∫⁻ t in Ici 0,
          ENNReal.ofReal (Real.exp (-lambda * t)) *
            Manhattan.annealedContinuousKernel t 0 0) =
          ENNReal.ofReal
            (Manhattan.Estimates.torusIntegral fun p₁ : ℝ =>
              Manhattan.Estimates.torusIntegral fun p₂ : ℝ =>
                (D.dissipativeSkewPair ![p₁, p₂]).resolventQuadratic
                  hlambda (Manhattan.walshL2 ∅)) := by
  refine ⟨Manhattan.concreteFiberEnvironment, rfl, rfl, fun p => rfl, ?_⟩
  intro lambda hlambda
  exact concrete_green_identity lambda hlambda

end Manhattan.Glue
