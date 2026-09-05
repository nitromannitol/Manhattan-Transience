import Manhattan.Glue.ScalarIdentification

/-!
# Degree-three multiplier energy

This file integrates the pointwise scalar core of Lemma 5.2 against the
honest raw correction constructed in `Walsh.Correction`. It also records the
precise interface needed to transport that estimate through the off-diagonal
Fourier projection to the synthesized Walsh vector.

Paper: `manuscript.tex:982-989`, `manuscript.tex:1200-1205`, and
`manuscript.tex:1257-1272`.
-/

open MeasureTheory

namespace Manhattan.Glue

noncomputable section

attribute [local instance] Real.fact_zero_lt_one

/-- The normalized Haar measure on the unit circle, named so that the
discharge files can share exactly this instance. -/
local instance cubicUnitAddCircleMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Total frequency `(β,r+r'-p₂)` of a raw type-`112` coefficient. -/
noncomputable def rawCorrectionTotalFrequency (p₂ : ℝ)
    (x : UnitAddTorus (Fin 3)) : Fin 2 → ℝ :=
  Estimates.mixedTotalFrequency (unitTorusAngle (x 2))
    (unitTorusAngle (x 0) + unitTorusAngle (x 1) - p₂)

/-- The integrated scalar core produced by the Finset raising calculation in
Lemma 5.2, before restricting away the coincident-row diagonal. -/
noncomputable def rawCubicCoreEnergy (q : Estimates.Parameters)
    (a p₂ : ℝ) : ℝ :=
  ∫ x : UnitAddTorus (Fin 3),
    Estimates.fourEstimateCore q (rawCorrectionTotalFrequency p₂ x) *
      ‖rawCorrectionFunction 40 q a p₂ x‖ ^ 2

/-- The raw multiplier quadratic form on the explicit correction. -/
noncomputable def rawCubicMultiplierEnergy (q : Estimates.Parameters)
    (a p₂ : ℝ) : ℝ :=
  ∫ x : UnitAddTorus (Fin 3),
    Estimates.multiplier 40 q (rawCorrectionTotalFrequency p₂ x) *
      ‖rawCorrectionFunction 40 q a p₂ x‖ ^ 2

private theorem rawCorrectionTotalFrequency_zero_measurable (p₂ : ℝ) :
    Measurable (fun x : UnitAddTorus (Fin 3) =>
      rawCorrectionTotalFrequency p₂ x 0) := by
  change Measurable (fun x : UnitAddTorus (Fin 3) => unitTorusAngle (x 2))
  exact unitTorusAngle_measurable.comp (measurable_pi_apply 2)

private theorem rawCorrectionTotalFrequency_one_measurable (p₂ : ℝ) :
    Measurable (fun x : UnitAddTorus (Fin 3) =>
      rawCorrectionTotalFrequency p₂ x 1) := by
  change Measurable (fun x : UnitAddTorus (Fin 3) =>
    unitTorusAngle (x 0) + unitTorusAngle (x 1) - p₂)
  have hzero : Measurable (fun x : UnitAddTorus (Fin 3) =>
      unitTorusAngle (x 0)) :=
    unitTorusAngle_measurable.comp (measurable_pi_apply 0)
  have hone : Measurable (fun x : UnitAddTorus (Fin 3) =>
      unitTorusAngle (x 1)) :=
    unitTorusAngle_measurable.comp (measurable_pi_apply 1)
  exact (hzero.add hone).sub measurable_const

private theorem rawCubicMultiplierIntegrand_measurable
    (q : Estimates.Parameters) (a p₂ : ℝ) :
    Measurable (fun x : UnitAddTorus (Fin 3) =>
      Estimates.multiplier 40 q (rawCorrectionTotalFrequency p₂ x) *
        ‖rawCorrectionFunction 40 q a p₂ x‖ ^ 2) := by
  have hmult : Measurable (fun x : UnitAddTorus (Fin 3) =>
      Estimates.multiplier 40 q (rawCorrectionTotalFrequency p₂ x)) := by
    have hzero : Measurable (fun x : UnitAddTorus (Fin 3) =>
        rawCorrectionTotalFrequency p₂ x 0) :=
      rawCorrectionTotalFrequency_zero_measurable p₂
    have hone : Measurable (fun x : UnitAddTorus (Fin 3) =>
        rawCorrectionTotalFrequency p₂ x 1) :=
      rawCorrectionTotalFrequency_one_measurable p₂
    unfold Estimates.multiplier Estimates.theta Estimates.dispersion
    fun_prop
  exact hmult.mul
    ((rawCorrectionFunction_measurable 40 q a p₂).norm.pow_const 2)


--; do not present it as
-- load-bearing when sealing.
private theorem rawCubicCoreIntegrand_measurable
    (q : Estimates.Parameters) (a p₂ : ℝ) :
    Measurable (fun x : UnitAddTorus (Fin 3) =>
      Estimates.fourEstimateCore q (rawCorrectionTotalFrequency p₂ x) *
        ‖rawCorrectionFunction 40 q a p₂ x‖ ^ 2) := by
  have hcore : Measurable (fun x : UnitAddTorus (Fin 3) =>
      Estimates.fourEstimateCore q (rawCorrectionTotalFrequency p₂ x)) := by
    have hzero : Measurable (fun x : UnitAddTorus (Fin 3) =>
        rawCorrectionTotalFrequency p₂ x 0) :=
      rawCorrectionTotalFrequency_zero_measurable p₂
    have hone : Measurable (fun x : UnitAddTorus (Fin 3) =>
        rawCorrectionTotalFrequency p₂ x 1) :=
      rawCorrectionTotalFrequency_one_measurable p₂
    unfold Estimates.fourEstimateCore Estimates.hWeight Estimates.theta
      Estimates.dispersion
    fun_prop
  exact hcore.mul
    ((rawCorrectionFunction_measurable 40 q a p₂).norm.pow_const 2)

private theorem multiplier_le_uniform (q : Estimates.Parameters)
    (P : Fin 2 → ℝ) :
    Estimates.multiplier 40 q P ≤ 40 * (q.lambda + 8) := by
  have hd0 : Estimates.dispersion (P 0) ≤ 2 := by
    unfold Estimates.dispersion
    linarith [Real.neg_one_le_cos (P 0)]
  have hd1 : Estimates.dispersion (P 1) ≤ 2 := by
    unfold Estimates.dispersion
    linarith [Real.neg_one_le_cos (P 1)]
  have hs0 := Real.abs_sin_le_one (P 0 / 2)
  have hs1 := Real.abs_sin_le_one (P 1 / 2)
  unfold Estimates.multiplier Estimates.theta
  nlinarith

private theorem rawCubicMultiplierEnergy_integrable {q : Estimates.Parameters}
    (hlambda : 0 < q.lambda) (a p₂ : ℝ) :
    Integrable (fun x : UnitAddTorus (Fin 3) =>
      Estimates.multiplier 40 q (rawCorrectionTotalFrequency p₂ x) *
        ‖rawCorrectionFunction 40 q a p₂ x‖ ^ 2) := by
  have hsquare : Integrable (fun x : UnitAddTorus (Fin 3) =>
      ‖rawCorrectionFunction 40 q a p₂ x‖ ^ 2) :=
    (rawCorrectionFunction_memLp (kappa := 40) (by norm_num)
      hlambda a p₂).integrable_norm_pow (by norm_num)
  apply Integrable.mono'
    (hsquare.const_mul (40 * (q.lambda + 8)))
    (rawCubicMultiplierIntegrand_measurable q a p₂).aestronglyMeasurable
  filter_upwards with x
  have hmultNonneg := Estimates.multiplier_nonneg
    (kappa := 40) (q := q) (by norm_num) hlambda.le
      (rawCorrectionTotalFrequency p₂ x)
  have hbound := multiplier_le_uniform q (rawCorrectionTotalFrequency p₂ x)
  have hsquareNonneg : 0 ≤ ‖rawCorrectionFunction 40 q a p₂ x‖ ^ 2 :=
    sq_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hmultNonneg hsquareNonneg)]
  exact mul_le_mul_of_nonneg_right hbound hsquareNonneg

private theorem fourEstimateCore_nonneg {q : Estimates.Parameters}
    (hlambda : 0 < q.lambda) (P : Fin 2 → ℝ) :
    0 ≤ Estimates.fourEstimateCore q P := by
  have hweight : 0 ≤ Estimates.hWeight q P :=
    (Estimates.hWeight_pos hlambda P).le
  have hden0 : 0 ≤ Real.sqrt
      (q.lambda + Estimates.dispersion (P 0)) := Real.sqrt_nonneg _
  have hden1 : 0 ≤ Real.sqrt
      (q.lambda + Estimates.dispersion (P 1)) := Real.sqrt_nonneg _
  have hzero : 0 ≤ Real.sin (P 0) ^ 2 /
      Real.sqrt (q.lambda + Estimates.dispersion (P 0)) :=
    div_nonneg (sq_nonneg _) hden0
  have hone : 0 ≤ Real.sin (P 1) ^ 2 /
      Real.sqrt (q.lambda + Estimates.dispersion (P 1)) :=
    div_nonneg (sq_nonneg _) hden1
  unfold Estimates.fourEstimateCore
  exact add_nonneg hweight
    (mul_nonneg (by norm_num) (add_nonneg hzero hone))

/-- Integrated Lemma 5.2 scalar core with the universal choice `κ=40`. -/
theorem rawCubicCoreEnergy_le_multiplier {q : Estimates.Parameters}
    (hlambda : 0 < q.lambda) (a p₂ : ℝ) :
    rawCubicCoreEnergy q a p₂ ≤ rawCubicMultiplierEnergy q a p₂ := by
  unfold rawCubicCoreEnergy rawCubicMultiplierEnergy
  exact integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun x => mul_nonneg
      (fourEstimateCore_nonneg hlambda (rawCorrectionTotalFrequency p₂ x))
      (sq_nonneg _))
    (rawCubicMultiplierEnergy_integrable hlambda a p₂)
    (Filter.Eventually.of_forall fun x =>
      mul_le_mul_of_nonneg_right
        (Estimates.fourEstimateCore_le_multiplier hlambda.le
          (rawCorrectionTotalFrequency p₂ x))
        (sq_nonneg _))

/-- `-- PARTIALLY discharged`: the complete Fourier--Walsh raising
calculation. It asserts that the concrete degree-three and degree-four
energies of the projected Walsh correction are dominated by the integrated raw
scalar core, and that off-diagonal projection is contractive for the
multiplier form.

The three forms are parameters so the assembly module can instantiate them
with its concrete degree-sector decomposition without creating an import
cycle. Status:

* the `multiplierForm` conjunct is `le_rfl` for the canonical form;
* the scalar core of the two sector bounds is
  `Manhattan.Glue.shiftedCorrectionWalsh_cubicCoreEnergy_le_of_sectors`
  (`Manhattan/Glue/CubicDischarge.lean`, the formalization);
* `ConcreteHThreeQuadraticBound` is proved at the momentum `(p₁,p₂)` by
  `Manhattan.Glue.concreteHThreeQuadraticBound`
  (`Manhattan/Glue/TransportDischarge.lean`, the formalization), using the ordered
  contractivity of `Manhattan/Glue/OrderedContractivity.lean`
  together with the `(shift)` phase of `Manhattan.type112ShiftTwist`;
* `ConcreteDThreeRaisingBound` is still unproved, but it is **no longer on the
  route to (23)**: the formalization proved summand 4 outright
  (`Manhattan.Glue.summandFourBound_proved`) and with it the grouped pair
  (`Manhattan.Glue.exists_summandTwoFourBound`), both in
  `Manhattan/Glue/SummandFourAssembly.lean`, so the live route is
  `summandTwoFourBound_of_summands` rather than
  `summandTwoFourBound_of_cubicSectors`. The only remaining input to (23) is
  `Manhattan.Glue.SummandThreeBound`; see the module docstring of
  `Manhattan/Glue/FinalDischarge.lean`. -/
def CubicWalshIntertwining (q : Estimates.Parameters)
    (hlambda : 0 < q.lambda) (a p₂ : ℝ)
    (hThree dFour multiplierForm : WalshL2 → ℝ) : Prop :=
  let k := correctionWalsh (kappa := 40) (by norm_num)
    hlambda a p₂
  hThree k + dFour k ≤ rawCubicCoreEnergy q a p₂ ∧
    rawCubicMultiplierEnergy q a p₂ ≤ multiplierForm k

/-- Lemma 5.2 in Walsh space, conditional only on the explicit
Fourier--Walsh intertwining interface above. Its analytic content is the
proved scalar theorem `rawCubicCoreEnergy_le_multiplier`. -/
theorem correctionWalsh_cubicEnergy_le_multiplier
    {q : Estimates.Parameters} (hlambda : 0 < q.lambda) (a p₂ : ℝ)
    (hThree dFour multiplierForm : WalshL2 → ℝ)
    (hintertwining : CubicWalshIntertwining q hlambda a p₂
      hThree dFour multiplierForm) :
    let k := correctionWalsh (kappa := 40) (by norm_num) hlambda a p₂
    hThree k + dFour k ≤ multiplierForm k := by
  dsimp
  exact hintertwining.1.trans <|
    (rawCubicCoreEnergy_le_multiplier hlambda a p₂).trans
      hintertwining.2

/-- Discharged: identification of
the Walsh multiplier quadratic form with the scalar `σ |v|²` term of (32).
The factor `2` is not slack: it is exactly the two disjoint summands of the
symmetrized coefficient, and equation (30) holds with it as an *identity*
(`Manhattan.Glue.rawCubicMultiplierEnergy_eq_two_correctionSigmaEnergy`).
Supplied for the canonical multiplier form by
`Manhattan.Glue.cubicMultiplierScalarIdentification_rawForm`
(`Manhattan/Glue/CubicDischarge.lean`), and for the concrete competitor by
`Manhattan.Glue.correctedCompetitor_cubicMultiplierScalarIdentification`
(`Manhattan/Glue/CubicDischargeProjection.lean`). Both are unconditional. -/
def CubicMultiplierScalarIdentification (q : Estimates.Parameters)
    (hlambda : 0 < q.lambda) (a p₂ : ℝ)
    (multiplierForm : WalshL2 → ℝ) : Prop :=
  let k := correctionWalsh (kappa := 40) (by norm_num)
    hlambda a p₂
  multiplierForm k ≤ 2 * correctionSigmaEnergy q a

/-- Proposition 4.2 turns the identified Walsh multiplier form into a
`2 C √L` estimate. -/
theorem correctionWalsh_multiplierEnergy_le_sqrtScale
    {q : Estimates.Parameters} (hlambda : 0 < q.lambda) {C a p₂ : ℝ}
    (multiplierForm : WalshL2 → ℝ)
    (hidentify : CubicMultiplierScalarIdentification q hlambda a p₂ multiplierForm)
    (hfive : Estimates.PropositionFiveTwoIntegralBound 40 C q a) :
    let k := correctionWalsh (kappa := 40) (by norm_num) hlambda a p₂
    multiplierForm k ≤ 2 * C * Real.sqrt (q.scaleLog a) := by
  dsimp
  calc
    multiplierForm
        (correctionWalsh (kappa := 40) (by norm_num) hlambda a p₂) ≤
        2 * correctionSigmaEnergy q a := hidentify
    _ ≤ 2 * (C * Real.sqrt (q.scaleLog a)) := by
      gcongr
      exact correctionSigmaEnergy_le_sqrtScale hlambda hfive
    _ = 2 * C * Real.sqrt (q.scaleLog a) := by ring

/-- Combined W7B handoff: Lemma 5.2 plus scalar identification bounds the
actual cubic energy by `2 C √L`. -/
theorem correctionWalsh_cubicEnergy_le_sqrtScale
    {q : Estimates.Parameters} (hlambda : 0 < q.lambda) {C a p₂ : ℝ}
    (hThree dFour multiplierForm : WalshL2 → ℝ)
    (hintertwining : CubicWalshIntertwining q hlambda a p₂
      hThree dFour multiplierForm)
    (hidentify : CubicMultiplierScalarIdentification q hlambda a p₂ multiplierForm)
    (hfive : Estimates.PropositionFiveTwoIntegralBound 40 C q a) :
    let k := correctionWalsh (kappa := 40) (by norm_num) hlambda a p₂
    hThree k + dFour k ≤ 2 * C * Real.sqrt (q.scaleLog a) := by
  dsimp
  exact (correctionWalsh_cubicEnergy_le_multiplier hlambda a p₂
    hThree dFour multiplierForm hintertwining).trans
      (correctionWalsh_multiplierEnergy_le_sqrtScale hlambda
        multiplierForm hidentify hfive)

/-- Complete W7B scalar handoff: after the raising and lowering modules supply
the two named intertwining interfaces, the cubic and mixed-residual energies
are bounded together by `4 C √L`. -/
theorem correctionWalsh_cubicAndMixedEnergy_le_sqrtScale
    {q : Estimates.Parameters} (hlambda : 0 < q.lambda)
    {C a p₂ mixedResidualEnergy : ℝ}
    (hThree dFour multiplierForm : WalshL2 → ℝ)
    (hcubic : CubicWalshIntertwining q hlambda a p₂
      hThree dFour multiplierForm)
    (hmultiplier : CubicMultiplierScalarIdentification q hlambda a p₂
      multiplierForm)
    (hmixed : MixedResidualScalarIdentification q a mixedResidualEnergy)
    (hfive : Estimates.PropositionFiveTwoIntegralBound 40 C q a) :
    let k := correctionWalsh (kappa := 40) (by norm_num) hlambda a p₂
    hThree k + dFour k + mixedResidualEnergy ≤
      4 * C * Real.sqrt (q.scaleLog a) := by
  dsimp
  have hcubicBound := correctionWalsh_cubicEnergy_le_sqrtScale
    hlambda hThree dFour multiplierForm hcubic hmultiplier hfive
  have hmixedBound := mixedResidualEnergy_le_sqrtScale
    hlambda hmixed hfive
  linarith

end

end Manhattan.Glue
