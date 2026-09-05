import Manhattan.Glue.ConcreteFiberization
import Manhattan.Glue.ConcreteGreen
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Pointwise concrete fibers on the vector-valued Fourier side

The frequency space is represented as the Hilbert sum of scalar torus `L²`
coordinates indexed by the complete Walsh basis.  Multiplication by a torus
character and permutation of Walsh coordinates therefore give the bounded
direct-integral realization of `p ↦ G_p`.

Paper: `manuscript.tex:555-597`.
-/

noncomputable section

open MeasureTheory UnitAddTorus
open scoped BigOperators ENNReal

namespace Manhattan.Glue

private theorem continuousLinearMap_ext_l2_single {I E F : Type*}
    [DecidableEq I]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [T2Space F]
    (T U : ℓ²(I, E) →L[ℂ] F)
    (h : ∀ i x, T (lp.single 2 i x) = U (lp.single 2 i x)) : T = U := by
  ext f
  have hf := lp.hasSum_single (p := (2 : ℝ≥0∞)) ENNReal.ofNat_ne_top f
  have hT := hf.map T T.continuous
  have hU := hf.map U U.continuous
  apply hT.unique
  have heq : (U ∘ fun i ↦ lp.single 2 i (f i)) =
      (T ∘ fun i ↦ lp.single 2 i (f i)) := by
    funext i
    exact (h i (f i)).symm
  rw [heq] at hU
  exact hU

/-- The scalar torus character carrying the positive phase `e^{ip·x}`. -/
def frequencyCharacter (x : Manhattan.Operator.Lattice)
    (t : UnitAddTorus (Fin 2)) : ℂ :=
  UnitAddTorus.mFourier x t

private theorem frequencyCharacter_memLp_top (x : Manhattan.Operator.Lattice) :
    MemLp (frequencyCharacter x) ∞
      (Measure.pi fun _ : Fin 2 ↦
        (AddCircle.haarAddCircle : Measure UnitAddCircle)) := by
  apply memLp_top_of_bound
    (UnitAddTorus.mFourier x).continuous.aestronglyMeasurable 1
  filter_upwards with t
  simp [UnitAddTorus.mFourier]

/-- Pointwise multiplication of a scalar `L²` function by a unit torus
character. -/
def frequencyPhaseMultiply (x : Manhattan.Operator.Lattice)
    (f : PositionFrequencyL2) : PositionFrequencyL2 :=
  ((Lp.memLp f).mul' (frequencyCharacter_memLp_top x)).toLp
    (fun t ↦ frequencyCharacter x t * f t)

theorem frequencyPhaseMultiply_apply_ae (x : Manhattan.Operator.Lattice)
    (f : PositionFrequencyL2) :
    frequencyPhaseMultiply x f =ᵐ[
      Measure.pi fun _ : Fin 2 ↦
        (AddCircle.haarAddCircle : Measure UnitAddCircle)]
      fun t ↦ frequencyCharacter x t * f t :=
  MemLp.coeFn_toLp ((Lp.memLp f).mul' (frequencyCharacter_memLp_top x))

private theorem frequencyPhaseMultiply_add (x : Manhattan.Operator.Lattice)
    (f g : PositionFrequencyL2) :
    frequencyPhaseMultiply x (f + g) =
      frequencyPhaseMultiply x f + frequencyPhaseMultiply x g := by
  apply Lp.ext
  filter_upwards [frequencyPhaseMultiply_apply_ae x (f + g),
    frequencyPhaseMultiply_apply_ae x f,
    frequencyPhaseMultiply_apply_ae x g, Lp.coeFn_add f g,
    Lp.coeFn_add (frequencyPhaseMultiply x f) (frequencyPhaseMultiply x g)]
    with t hfg hf hg hadd hadd'
  have hadd_t : (f + g) t = f t + g t := by
    simpa only [Pi.add_apply] using hadd
  have hadd'_t : (frequencyPhaseMultiply x f +
      frequencyPhaseMultiply x g) t =
      frequencyPhaseMultiply x f t + frequencyPhaseMultiply x g t := by
    simpa only [Pi.add_apply] using hadd'
  calc
    frequencyPhaseMultiply x (f + g) t =
        frequencyCharacter x t * (f + g) t := hfg
    _ = frequencyCharacter x t * (f t + g t) := by rw [hadd_t]
    _ = frequencyCharacter x t * f t +
        frequencyCharacter x t * g t := mul_add _ _ _
    _ = frequencyPhaseMultiply x f t +
        frequencyPhaseMultiply x g t := by rw [hf, hg]
    _ = (frequencyPhaseMultiply x f +
        frequencyPhaseMultiply x g) t := hadd'_t.symm

private theorem frequencyPhaseMultiply_smul (x : Manhattan.Operator.Lattice)
    (c : ℂ) (f : PositionFrequencyL2) :
    frequencyPhaseMultiply x (c • f) = c • frequencyPhaseMultiply x f := by
  apply Lp.ext
  filter_upwards [frequencyPhaseMultiply_apply_ae x (c • f),
    frequencyPhaseMultiply_apply_ae x f, Lp.coeFn_smul c f,
    Lp.coeFn_smul c (frequencyPhaseMultiply x f)] with t hcf hf hsmul hsmul'
  have hsmul_t : (c • f) t = c * f t := by
    simpa only [Pi.smul_apply, smul_eq_mul] using hsmul
  have hsmul'_t : (c • frequencyPhaseMultiply x f) t =
      c * frequencyPhaseMultiply x f t := by
    simpa only [Pi.smul_apply, smul_eq_mul] using hsmul'
  calc
    frequencyPhaseMultiply x (c • f) t =
        frequencyCharacter x t * (c • f) t := hcf
    _ = frequencyCharacter x t * (c * f t) := by rw [hsmul_t]
    _ = c * (frequencyCharacter x t * f t) := by ring
    _ = c * frequencyPhaseMultiply x f t := by rw [hf]
    _ = (c • frequencyPhaseMultiply x f) t := hsmul'_t.symm

private theorem frequencyPhaseMultiply_norm (x : Manhattan.Operator.Lattice)
    (f : PositionFrequencyL2) : ‖frequencyPhaseMultiply x f‖ = ‖f‖ := by
  unfold frequencyPhaseMultiply
  rw [Lp.norm_toLp, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae
  filter_upwards with t
  simp [frequencyCharacter, UnitAddTorus.mFourier]

/-- The unitary positive-phase multiplier on scalar torus `L²`.  Unlike a
definition by Fourier conjugation, this is constructed from pointwise
multiplication, so the later fiberization equality is not circular. -/
def frequencyPhaseMultiplier (x : Manhattan.Operator.Lattice) :
    PositionFrequencyL2 ≃ₗᵢ[ℂ] PositionFrequencyL2 where
  toFun := frequencyPhaseMultiply x
  invFun := frequencyPhaseMultiply (-x)
  left_inv f := by
    apply Lp.ext
    filter_upwards [frequencyPhaseMultiply_apply_ae (-x)
        (frequencyPhaseMultiply x f),
      frequencyPhaseMultiply_apply_ae x f] with t hneg hx
    rw [hneg, hx]
    change UnitAddTorus.mFourier (-x) t *
      (UnitAddTorus.mFourier x t * f t) = f t
    rw [← mul_assoc, ← UnitAddTorus.mFourier_add]
    simp [UnitAddTorus.mFourier]
  right_inv f := by
    apply Lp.ext
    filter_upwards [frequencyPhaseMultiply_apply_ae x
        (frequencyPhaseMultiply (-x) f),
      frequencyPhaseMultiply_apply_ae (-x) f] with t hx hneg
    rw [hx, hneg]
    change UnitAddTorus.mFourier x t *
      (UnitAddTorus.mFourier (-x) t * f t) = f t
    rw [← mul_assoc, ← UnitAddTorus.mFourier_add]
    simp [UnitAddTorus.mFourier]
  map_add' := frequencyPhaseMultiply_add x
  map_smul' := frequencyPhaseMultiply_smul x
  norm_map' := frequencyPhaseMultiply_norm x

/-- A negative Fourier monomial acquires the positive shift phase. -/
@[simp] theorem frequencyPhaseMultiplier_mFourierLp
    (x z : Manhattan.Operator.Lattice) :
    frequencyPhaseMultiplier x (mFourierLp 2 (-z)) =
      mFourierLp 2 (-(z - x)) := by
  apply Lp.ext
  filter_upwards [frequencyPhaseMultiply_apply_ae x (mFourierLp 2 (-z)),
    UnitAddTorus.coeFn_mFourierLp (2 : ℝ≥0∞) (-z),
    UnitAddTorus.coeFn_mFourierLp (2 : ℝ≥0∞) (-(z - x))]
    with t hphase hz htarget
  change frequencyPhaseMultiply x (mFourierLp 2 (-z)) t =
    mFourierLp 2 (-(z - x)) t
  rw [hphase, hz, htarget]
  change UnitAddTorus.mFourier x t * UnitAddTorus.mFourier (-z) t =
    UnitAddTorus.mFourier (-(z - x)) t
  rw [mul_comm, ← UnitAddTorus.mFourier_add]
  congr 2
  module

private theorem positionArgumentShift_single (x z : Manhattan.Operator.Lattice) :
    positionArgumentShift x (lp.single 2 z (1 : ℂ)) =
      lp.single 2 (z - x) (1 : ℂ) := by
  apply lp.ext
  funext w
  rw [positionArgumentShift_apply]
  by_cases hw : w = z - x
  · subst w
    simp
  · have hwx : w + x ≠ z := by
      intro heq
      apply hw
      exact eq_sub_of_add_eq heq
    simp [lp.single_apply, hw, hwx]

/-- Scalar form of the negative-phase Fourier shift intertwining. -/
theorem negativePositionFourier_positionArgumentShift
    (x : Manhattan.Operator.Lattice) (f : Manhattan.Operator.PositionL2) :
    negativePositionFourier (positionArgumentShift x f) =
      frequencyPhaseMultiplier x (negativePositionFourier f) := by
  let T : Manhattan.Operator.PositionL2 →L[ℂ] PositionFrequencyL2 :=
    negativePositionFourier.toLinearIsometry.toContinuousLinearMap ∘L
      (positionArgumentShift x).toLinearIsometry.toContinuousLinearMap
  let U : Manhattan.Operator.PositionL2 →L[ℂ] PositionFrequencyL2 :=
    (frequencyPhaseMultiplier x).toLinearIsometry.toContinuousLinearMap ∘L
      negativePositionFourier.toLinearIsometry.toContinuousLinearMap
  have hTU : T = U := by
    apply continuousLinearMap_ext_l2_single
    intro z a
    have hsingle : (lp.single 2 z a : Manhattan.Operator.PositionL2) =
        a • (lp.single 2 z (1 : ℂ) : Manhattan.Operator.PositionL2) := by
      simpa using (lp.single_smul (E := fun _ : Manhattan.Operator.Lattice ↦ ℂ)
        (2 : ℝ≥0∞) z a (1 : ℂ))
    simp only [T, U, ContinuousLinearMap.comp_apply]
    rw [hsingle]
    simp only [map_smul]
    change a • negativePositionFourier
        (positionArgumentShift x (lp.single 2 z (1 : ℂ))) =
      a • frequencyPhaseMultiplier x
        (negativePositionFourier (lp.single 2 z (1 : ℂ)))
    rw [positionArgumentShift_single, negativePositionFourier_single,
      negativePositionFourier_single, frequencyPhaseMultiplier_mFourierLp]
  exact DFunLike.congr_fun hTU f

/-- Walsh-coordinate realization of the pointwise phase-and-translation
operator in a fiber. -/
noncomputable def fiberwiseTranslatedStep (x : Manhattan.Operator.Lattice) :
    JointFrequencyL2 ≃ₗᵢ[ℂ] JointFrequencyL2 :=
  (l2CongrLeft (translateWalshIndexEquiv x)).trans
    (l2CongrRight (frequencyPhaseMultiplier x))

/-- Walsh-coordinate realization of multiplication by the origin sign in
every fiber. -/
noncomputable def fiberwiseOriginSign (i : Fin 2) :
    JointFrequencyL2 ≃ₗᵢ[ℂ] JointFrequencyL2 :=
  l2CongrLeft (toggleOriginWalshIndexEquiv i)

/-- The pointwise symmetric fiber summand. -/
noncomputable def fiberwiseSymmetricTerm (i : Fin 2) :
    JointFrequencyL2 →L[ℂ] JointFrequencyL2 :=
  (fiberwiseTranslatedStep (Manhattan.Operator.axisVector i)).toLinearIsometry.toContinuousLinearMap +
    (fiberwiseTranslatedStep (-Manhattan.Operator.axisVector i)).toLinearIsometry.toContinuousLinearMap -
    (2 : ℂ) • ContinuousLinearMap.id ℂ JointFrequencyL2

/-- The pointwise antisymmetric fiber summand. -/
noncomputable def fiberwiseSkewTerm (i : Fin 2) :
    JointFrequencyL2 →L[ℂ] JointFrequencyL2 :=
  (fiberwiseOriginSign i).toLinearIsometry.toContinuousLinearMap ∘L
    ((fiberwiseTranslatedStep (Manhattan.Operator.axisVector i)).toLinearIsometry.toContinuousLinearMap -
      (fiberwiseTranslatedStep (-Manhattan.Operator.axisVector i)).toLinearIsometry.toContinuousLinearMap)

/-- The bounded direct-integral realization of
`p ↦ concreteFiberEnvironment.fiberGenerator p`.  Its Walsh coordinates
are mixed by translations and origin-sign toggles, while each scalar torus
coordinate is multiplied pointwise by the corresponding character. -/
noncomputable def concreteFiberDirectIntegral :
    JointFrequencyL2 →L[ℂ] JointFrequencyL2 :=
  (2 : ℂ)⁻¹ • ∑ i : Fin 2,
    (fiberwiseSymmetricTerm i + fiberwiseSkewTerm i)

/-- The real representative in `(-π,π]²` of a point on Mathlib's
normalized additive torus. -/
noncomputable def torusFrequency (t : UnitAddTorus (Fin 2)) : Fin 2 → ℝ :=
  fun i ↦ 2 * Real.pi *
    (AddCircle.measurableEquivIoc 1 (-(1 / 2 : ℝ)) (t i)).1

theorem exp_torusFrequency_eq_frequencyCharacter
    (t : UnitAddTorus (Fin 2)) (i : Fin 2) :
    Complex.exp (Complex.I * torusFrequency t i) =
      frequencyCharacter (Manhattan.Operator.axisVector i) t := by
  let a := AddCircle.measurableEquivIoc 1 (-(1 / 2 : ℝ)) (t i)
  have ha : ((a.1 : ℝ) : UnitAddCircle) = t i := by
    change (AddCircle.measurableEquivIoc 1
      (-(1 / 2 : ℝ))).symm ((AddCircle.measurableEquivIoc 1
        (-(1 / 2 : ℝ))) (t i)) = t i
    exact (AddCircle.measurableEquivIoc 1
      (-(1 / 2 : ℝ))).symm_apply_apply (t i)
  change Complex.exp (Complex.I * ((2 * Real.pi * a.1 : ℝ) : ℂ)) = _
  rw [frequencyCharacter]
  change _ = UnitAddTorus.mFourier (Pi.single i 1) t
  rw [UnitAddTorus.mFourier_single, ← ha, fourier_coe_apply]
  congr 1
  push_cast
  ring

theorem exp_neg_torusFrequency_eq_frequencyCharacter
    (t : UnitAddTorus (Fin 2)) (i : Fin 2) :
    Complex.exp (-Complex.I * torusFrequency t i) =
      frequencyCharacter (-Manhattan.Operator.axisVector i) t := by
  rw [show -Manhattan.Operator.axisVector i =
      -(Manhattan.Operator.axisVector i) by rfl,
    frequencyCharacter, UnitAddTorus.mFourier_neg]
  change Complex.exp (-Complex.I * torusFrequency t i) =
    starRingEnd ℂ (frequencyCharacter (Manhattan.Operator.axisVector i) t)
  rw [← exp_torusFrequency_eq_frequencyCharacter t i,
    ← Complex.exp_conj]
  congr 1
  simp

/-- The concrete fiber generator written intrinsically at a point of
Mathlib's normalized torus.  This is the same finite operator formula as
`concreteFiberEnvironment.fiberGenerator`, with its exponential phases
represented by torus characters. -/
noncomputable def torusFiberGenerator (t : UnitAddTorus (Fin 2)) :
    Manhattan.WalshL2 →L[ℂ] Manhattan.WalshL2 :=
  (2 : ℂ)⁻¹ • ∑ i : Fin 2,
    ((frequencyCharacter (Manhattan.Operator.axisVector i) t) •
          Manhattan.environmentShift (Manhattan.Operator.axisVector i) +
        (frequencyCharacter (-Manhattan.Operator.axisVector i) t) •
          Manhattan.environmentShift (-Manhattan.Operator.axisVector i) -
        (2 : ℂ) • ContinuousLinearMap.id ℂ Manhattan.WalshL2 +
      Manhattan.originSignMultiplier i ∘L
        ((frequencyCharacter (Manhattan.Operator.axisVector i) t) •
            Manhattan.environmentShift (Manhattan.Operator.axisVector i) -
          (frequencyCharacter (-Manhattan.Operator.axisVector i) t) •
            Manhattan.environmentShift (-Manhattan.Operator.axisVector i)))

/-- The bounded pointwise fiber field is continuous, hence strongly
measurable for direct-integration purposes. -/
theorem continuous_torusFiberGenerator : Continuous torusFiberGenerator := by
  unfold torusFiberGenerator frequencyCharacter
  simp only [Fin.sum_univ_two]
  fun_prop

/-- Any real lift whose positive and negative exponentials are the torus
characters gives exactly the certified concrete fiber generator. -/
theorem torusFiberGenerator_eq_concreteFiberGenerator
    (t : UnitAddTorus (Fin 2)) (p : Fin 2 → ℝ)
    (hplus : ∀ i, Complex.exp (Complex.I * p i) =
      frequencyCharacter (Manhattan.Operator.axisVector i) t)
    (hminus : ∀ i, Complex.exp (-Complex.I * p i) =
      frequencyCharacter (-Manhattan.Operator.axisVector i) t) :
    torusFiberGenerator t =
      Manhattan.concreteFiberEnvironment.fiberGenerator p := by
  unfold torusFiberGenerator Manhattan.Operator.FiberEnvironment.fiberGenerator
  change _ = Manhattan.concreteFiberS p + Manhattan.concreteFiberA p
  rw [Manhattan.concreteFiberS_formula, Manhattan.concreteFiberA_formula]
  simp_rw [hplus, hminus]
  rw [← smul_add, ← Finset.sum_add_distrib]

/-- Every torus point has its canonical real representative, and the
intrinsic torus fiber is exactly the certified generator at that
representative. -/
theorem torusFiberGenerator_eq_concreteFiberGenerator_torusFrequency
    (t : UnitAddTorus (Fin 2)) :
    torusFiberGenerator t =
      Manhattan.concreteFiberEnvironment.fiberGenerator (torusFrequency t) :=
  torusFiberGenerator_eq_concreteFiberGenerator t (torusFrequency t)
    (exp_torusFrequency_eq_frequencyCharacter t)
    (exp_neg_torusFrequency_eq_frequencyCharacter t)

/-- Exact Walsh-coordinate formula for the direct integral.  Together with
`frequencyPhaseMultiply_apply_ae`, this states pointwise (almost
everywhere) application of `torusFiberGenerator`. -/
theorem concreteFiberDirectIntegral_coordinate
    (K : JointFrequencyL2) (S : Finset LineIndex) :
    concreteFiberDirectIntegral K S =
      (2 : ℂ)⁻¹ • ∑ i : Fin 2,
        (frequencyPhaseMultiplier (Manhattan.Operator.axisVector i)
              (K ((translateWalshIndexEquiv
                (Manhattan.Operator.axisVector i)).symm S)) +
          frequencyPhaseMultiplier (-Manhattan.Operator.axisVector i)
              (K ((translateWalshIndexEquiv
                (-Manhattan.Operator.axisVector i)).symm S)) -
          (2 : ℂ) • K S +
          (frequencyPhaseMultiplier (Manhattan.Operator.axisVector i)
                (K ((translateWalshIndexEquiv
                  (Manhattan.Operator.axisVector i)).symm
                    ((toggleOriginWalshIndexEquiv i).symm S))) -
            frequencyPhaseMultiplier (-Manhattan.Operator.axisVector i)
                (K ((translateWalshIndexEquiv
                  (-Manhattan.Operator.axisVector i)).symm
                    ((toggleOriginWalshIndexEquiv i).symm S))))) := by
  simp [concreteFiberDirectIntegral, fiberwiseSymmetricTerm,
    fiberwiseSkewTerm, fiberwiseTranslatedStep, fiberwiseOriginSign]

/-- The vector Fourier transform carries each joint translated step to its
independently defined pointwise fiber step. -/
theorem jointPositionFourier_jointTranslatedStep
    (x : Manhattan.Operator.Lattice) (F : JointPositionL2) :
    jointPositionFourier (jointTranslatedStep x F) =
      fiberwiseTranslatedStep x (jointPositionFourier F) := by
  apply lp.ext
  funext S
  simp only [jointPositionFourier, jointTranslatedStep,
    fiberwiseTranslatedStep, LinearIsometryEquiv.trans_apply,
    l2CongrLeft_apply, l2CongrRight_apply]
  exact negativePositionFourier_positionArgumentShift x
    (F ((translateWalshIndexEquiv x).symm S))

/-- The origin-sign Walsh permutation commutes with position Fourier
transform. -/
theorem jointPositionFourier_jointOriginSign (i : Fin 2)
    (F : JointPositionL2) :
    jointPositionFourier (jointOriginSign i F) =
      fiberwiseOriginSign i (jointPositionFourier F) := by
  apply lp.ext
  funext S
  rfl

private theorem jointPositionFourier_jointSymmetricTerm (i : Fin 2)
    (F : JointPositionL2) :
    jointPositionFourier (jointSymmetricTerm i F) =
      fiberwiseSymmetricTerm i (jointPositionFourier F) := by
  simp only [jointSymmetricTerm, fiberwiseSymmetricTerm,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    map_sub, map_add, map_smul]
  change jointPositionFourier
      (jointTranslatedStep (Manhattan.Operator.axisVector i) F) +
      jointPositionFourier
        (jointTranslatedStep (-Manhattan.Operator.axisVector i) F) -
      2 • jointPositionFourier F =
    fiberwiseTranslatedStep (Manhattan.Operator.axisVector i)
        (jointPositionFourier F) +
      fiberwiseTranslatedStep (-Manhattan.Operator.axisVector i)
        (jointPositionFourier F) -
      2 • jointPositionFourier F
  rw [jointPositionFourier_jointTranslatedStep,
    jointPositionFourier_jointTranslatedStep]

private theorem jointPositionFourier_jointSkewTerm (i : Fin 2)
    (F : JointPositionL2) :
    jointPositionFourier (jointSkewTerm i F) =
      fiberwiseSkewTerm i (jointPositionFourier F) := by
  simp only [jointSkewTerm, fiberwiseSkewTerm,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply, map_sub]
  change jointPositionFourier
      (jointOriginSign i
        (jointTranslatedStep (Manhattan.Operator.axisVector i) F)) -
      jointPositionFourier
        (jointOriginSign i
          (jointTranslatedStep (-Manhattan.Operator.axisVector i) F)) =
    fiberwiseOriginSign i
        (fiberwiseTranslatedStep (Manhattan.Operator.axisVector i)
          (jointPositionFourier F)) -
      fiberwiseOriginSign i
        (fiberwiseTranslatedStep (-Manhattan.Operator.axisVector i)
          (jointPositionFourier F))
  rw [jointPositionFourier_jointOriginSign,
    jointPositionFourier_jointOriginSign]
  rw [jointPositionFourier_jointTranslatedStep,
    jointPositionFourier_jointTranslatedStep]

/-- The concrete joint generator is transformed into the explicitly
pointwise direct-integral fiber operator. -/
theorem jointPositionFourier_concreteJointGenerator (F : JointPositionL2) :
    jointPositionFourier (concreteJointGenerator F) =
      concreteFiberDirectIntegral (jointPositionFourier F) := by
  simp only [concreteJointGenerator, concreteFiberDirectIntegral,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.add_apply, map_smul, map_sum, map_add]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [jointPositionFourier_jointSymmetricTerm,
    jointPositionFourier_jointSkewTerm]

/-- Proposition-generator v2's operator identity: the previously certified
Fourier conjugate is exactly the independently constructed direct integral
of the concrete pointwise fibers. -/
theorem concreteJointFiberOperator_eq_directIntegral :
    concreteJointFiberOperator = concreteFiberDirectIntegral := by
  apply ContinuousLinearMap.ext
  intro K
  let F : JointPositionL2 := jointPositionFourier.symm K
  calc
    concreteJointFiberOperator K =
        concreteJointFiberOperator (jointPositionFourier F) := by
      rw [show jointPositionFourier F = K by
        exact jointPositionFourier.apply_symm_apply K]
    _ = jointPositionFourier (concreteJointGenerator F) :=
      (concreteJointGenerator_fiberizes F).symm
    _ = concreteFiberDirectIntegral (jointPositionFourier F) :=
      jointPositionFourier_concreteJointGenerator F
    _ = concreteFiberDirectIntegral K := by
      rw [show jointPositionFourier F = K by
        exact jointPositionFourier.apply_symm_apply K]

/-- Shift and origin-sign identification determine the fiber generator
formula, hence identify any Proposition 2.1 witness with the concrete
generator used by the pointwise direct integral. -/
theorem fiberGenerator_eq_concrete_of_shift_omega
    (D : Manhattan.Operator.FiberEnvironment Manhattan.WalshL2)
    (hshift : D.shift = Manhattan.environmentShift)
    (homega : D.omega = Manhattan.originSignMultiplier)
    (p : Fin 2 → ℝ) :
    D.fiberGenerator p =
      Manhattan.concreteFiberEnvironment.fiberGenerator p := by
  unfold Manhattan.Operator.FiberEnvironment.fiberGenerator
  rw [D.fiberS_formula, D.fiberA_formula,
    Manhattan.concreteFiberEnvironment.fiberS_formula,
    Manhattan.concreteFiberEnvironment.fiberA_formula,
    hshift, homega]
  rfl

/-- Frozen-block-ready version 2 of Proposition 2.1.  In addition to the
original generator and Green identity, it exposes the actual pointwise
torus fibers and identifies their direct integral with the conjugated joint
generator. -/
theorem proposition_generator_v2 :
    ∃ D : Manhattan.Operator.FiberEnvironment Manhattan.WalshL2,
      D.shift = Manhattan.environmentShift ∧
      D.omega = Manhattan.originSignMultiplier ∧
      (∀ p : Fin 2 → ℝ,
        D.fiberGenerator p = D.fiberS p + D.fiberA p) ∧
      (∀ t : UnitAddTorus (Fin 2),
        torusFiberGenerator t = D.fiberGenerator (torusFrequency t)) ∧
      concreteJointFiberOperator = concreteFiberDirectIntegral ∧
      ∀ (lambda : ℝ), ∀ hlambda : 0 < lambda,
        (∫⁻ s in Set.Ici 0,
          ENNReal.ofReal (Real.exp (-lambda * s)) *
            Manhattan.annealedContinuousKernel s 0 0) =
          ENNReal.ofReal
            (Manhattan.Estimates.torusIntegral fun p₁ : ℝ ↦
              Manhattan.Estimates.torusIntegral fun p₂ : ℝ ↦
                (D.dissipativeSkewPair ![p₁, p₂]).resolventQuadratic
                  hlambda (Manhattan.walshL2 ∅)) := by
  obtain ⟨D, hshift, homega, hgenerator, hgreen⟩ := proposition_generator
  refine ⟨D, hshift, homega, hgenerator, ?_,
    concreteJointFiberOperator_eq_directIntegral, hgreen⟩
  intro t
  calc
    torusFiberGenerator t =
        Manhattan.concreteFiberEnvironment.fiberGenerator (torusFrequency t) :=
      torusFiberGenerator_eq_concreteFiberGenerator_torusFrequency t
    _ = D.fiberGenerator (torusFrequency t) :=
      (fiberGenerator_eq_concrete_of_shift_omega D hshift homega
        (torusFrequency t)).symm

end Manhattan.Glue
