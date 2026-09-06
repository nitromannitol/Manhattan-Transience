# Correspondence: paper ↔ Lean

This table maps every frozen public declaration to *The randomly oriented
Manhattan lattice in 2D is transient* (Bou-Rabee--Peres).

## Conventions

- Lean names are relative to the `Manhattan` namespace; file paths are
  repository-relative.
- Source locations cite the pinned file as `manuscript.tex:<line>` or
  `manuscript.tex:<start>-<end>`. The full source SHA-256 is in
  `ledger/manifest.yaml`.
- Every manifest node appears exactly once below, including meaning-carrying
  definitions. Conversely, every row names exactly one manifest node.
- Status is `definition` for a frozen definition, `draft (statement)` for an
  exact statement with a registered placeholder, `sealed` for a proved
  statement whose reading against the manuscript has been recorded once, and
  `proved` once a second reading agrees. Retired proved rows remain as history and name their
  approved successor. A frozen statement is not itself a proof claim.
- Encoding or normalization choices, deviations and source ambiguities are
  described in the row itself; they are never silently absorbed.

The table below is the complete frozen surface; counts and states are checked
against `ledger/manifest.yaml`. As of 2026-09-04 that manifest has **76 nodes,
all in state `PROVED`** and none `DRAFT_SORRY`; each has exactly one row below.
Twelve of them are the concrete-lemma anchors, whose second reading is not yet
recorded, so those rows and the four rows for the main theorems read `sealed`.

| Source / manifest node | Lean declaration | File | Status |
|---|---|---|---|
| `manuscript.tex:564-607` / `op-damped-orbit-has-deriv-at` | `Manhattan.Frozen.Operator.dampedOrbit_hasDerivAt` | `Manhattan/Frozen/Operator/DampedOrbitHasDerivAt.lean` | proved |
| `manuscript.tex:564-607` / `op-damped-orbit-norm-le` | `Manhattan.Frozen.Operator.dampedOrbit_norm_le` | `Manhattan/Frozen/Operator/DampedOrbitNormLe.lean` | proved |
| `manuscript.tex:576-585` / `op-fiber-a-eq-formula` | `Manhattan.Frozen.Operator.fiberA_eq_formula` | `Manhattan/Frozen/Operator/FiberAEqFormula.lean` | proved |
| `manuscript.tex:576-585` / `op-fiber-a-norm-le` | `Manhattan.Frozen.Operator.fiberA_norm_le` | `Manhattan/Frozen/Operator/FiberANormLe.lean` | proved |
| `manuscript.tex:576-585` / `op-fiber-a-skew-adjoint` | `Manhattan.Frozen.Operator.fiberA_skewAdjoint` | `Manhattan/Frozen/Operator/FiberASkewAdjoint.lean` | proved |
| `manuscript.tex:576-585` / `op-fiber-s-eq-formula` | `Manhattan.Frozen.Operator.fiberS_eq_formula` | `Manhattan/Frozen/Operator/FiberSEqFormula.lean` | proved |
| `manuscript.tex:576-585` / `op-fiber-s-nonpositive` | `Manhattan.Frozen.Operator.fiberS_nonpositive` | `Manhattan/Frozen/Operator/FiberSNonpositive.lean` | proved |
| `manuscript.tex:576-585` / `op-fiber-s-norm-le` | `Manhattan.Frozen.Operator.fiberS_norm_le` | `Manhattan/Frozen/Operator/FiberSNormLe.lean` | proved |
| `manuscript.tex:576-585` / `op-fiber-s-self-adjoint` | `Manhattan.Frozen.Operator.fiberS_selfAdjoint` | `Manhattan/Frozen/Operator/FiberSSelfAdjoint.lean` | proved |
| `manuscript.tex:640-666` / `op-frequency-resolvent-le-of-competitor` | `Manhattan.Frozen.Operator.frequency_resolvent_le_of_competitor` | `Manhattan/Frozen/Operator/FrequencyResolventLeOfCompetitor.lean` | proved (retired; superseded by `op-frequency-resolvent-le-of-competitor-v2`) |
| `manuscript.tex:640-666` / `op-frequency-resolvent-le-of-competitor-v2` | `Manhattan.Frozen.Operator.frequency_resolvent_le_of_competitor_v2` | `Manhattan/Frozen/Operator/FrequencyResolventLeOfCompetitorV2.lean` | proved (second reading recorded) |
| `manuscript.tex:564-607` / `op-generator-commutes-operator-semigroup` | `Manhattan.Frozen.Operator.generator_commutes_operatorSemigroup` | `Manhattan/Frozen/Operator/GeneratorCommutesOperatorSemigroup.lean` | proved |
| `manuscript.tex:610-638` / `op-h-bijective` | `Manhattan.Frozen.Operator.H_bijective` | `Manhattan/Frozen/Operator/HBijective.lean` | proved |
| `manuscript.tex:564-607` / `op-integrable-on-damped-orbit` | `Manhattan.Frozen.Operator.integrableOn_dampedOrbit` | `Manhattan/Frozen/Operator/IntegrableOnDampedOrbit.lean` | proved |
| `manuscript.tex:564-607` / `op-integrable-on-resolvent-damped-orbit` | `Manhattan.Frozen.Operator.integrableOn_resolvent_dampedOrbit` | `Manhattan/Frozen/Operator/IntegrableOnResolventDampedOrbit.lean` | proved |
| `manuscript.tex:564-607` / `op-integral-inner-operator-semigroup-eq-resolvent` | `Manhattan.Frozen.Operator.integral_inner_operatorSemigroup_eq_resolvent` | `Manhattan/Frozen/Operator/IntegralInnerOperatorSemigroupEqResolvent.lean` | proved |
| `manuscript.tex:564-607` / `op-laplace-vector-resolvent-operator` | `Manhattan.Frozen.Operator.laplaceVector_resolventOperator` | `Manhattan/Frozen/Operator/LaplaceVectorResolventOperator.lean` | proved |
| `manuscript.tex:668-681` / `op-logarithmic-tail-eq-two` | `Manhattan.Frozen.Operator.logarithmicTail_eq_two` | `Manhattan/Frozen/Operator/LogarithmicTailEqTwo.lean` | proved |
| `manuscript.tex:610-638` / `op-minus-bijective` | `Manhattan.Frozen.Operator.minus_bijective` | `Manhattan/Frozen/Operator/MinusBijective.lean` | proved |
| `manuscript.tex:564-607` / `op-operator-semigroup-has-deriv-at` | `Manhattan.Frozen.Operator.operatorSemigroup_hasDerivAt` | `Manhattan/Frozen/Operator/OperatorSemigroupHasDerivAt.lean` | proved |
| `manuscript.tex:610-638` / `op-plus-bijective` | `Manhattan.Frozen.Operator.plus_bijective` | `Manhattan/Frozen/Operator/PlusBijective.lean` | proved |
| `manuscript.tex:568-570` / `op-position-fourier-norm` | `Manhattan.Frozen.Operator.positionFourier_norm` | `Manhattan/Frozen/Operator/PositionFourierNorm.lean` | proved |
| `manuscript.tex:568-570` / `op-position-fourier-single` | `Manhattan.Frozen.Operator.positionFourier_single` | `Manhattan/Frozen/Operator/PositionFourierSingle.lean` | proved |
| `manuscript.tex:610-638` / `op-real-form-h-coercive` | `Manhattan.Frozen.Operator.realForm_H_coercive` | `Manhattan/Frozen/Operator/RealFormHCoercive.lean` | proved |
| `manuscript.tex:610-638` / `op-real-form-minus-coercive` | `Manhattan.Frozen.Operator.realForm_minus_coercive` | `Manhattan/Frozen/Operator/RealFormMinusCoercive.lean` | proved |
| `manuscript.tex:610-638` / `op-real-form-plus-coercive` | `Manhattan.Frozen.Operator.realForm_plus_coercive` | `Manhattan/Frozen/Operator/RealFormPlusCoercive.lean` | proved |
| `manuscript.tex:564-607` / `op-resolvent-equiv-symm-apply` | `Manhattan.Frozen.Operator.resolventEquiv_symm_apply` | `Manhattan/Frozen/Operator/ResolventEquivSymmApply.lean` | proved |
| `manuscript.tex:564-607` / `op-resolvent-operator-bijective` | `Manhattan.Frozen.Operator.resolventOperator_bijective` | `Manhattan/Frozen/Operator/ResolventOperatorBijective.lean` | proved |
| `manuscript.tex:564-607` / `op-resolvent-operator-injective` | `Manhattan.Frozen.Operator.resolventOperator_injective` | `Manhattan/Frozen/Operator/ResolventOperatorInjective.lean` | proved |
| `manuscript.tex:564-607` / `op-resolvent-operator-laplace-vector` | `Manhattan.Frozen.Operator.resolventOperator_laplaceVector` | `Manhattan/Frozen/Operator/ResolventOperatorLaplaceVector.lean` | proved |
| `manuscript.tex:626-638` / `var-ineq` | `Manhattan.Frozen.Operator.resolventQuadratic_le` | `Manhattan/Frozen/Operator/ResolventQuadraticLe.lean` | proved |
| `manuscript.tex:610-638` / `op-resolvent-quadratic-le-h-minus-energy` | `Manhattan.Frozen.Operator.resolventQuadratic_le_hMinusEnergy` | `Manhattan/Frozen/Operator/ResolventQuadraticLeHMinusEnergy.lean` | proved |
| `manuscript.tex:564-607` / `op-tendsto-damped-orbit-at-top` | `Manhattan.Frozen.Operator.tendsto_dampedOrbit_atTop` | `Manhattan/Frozen/Operator/TendstoDampedOrbitAtTop.lean` | proved |
| `manuscript.tex:668-681` / `op-uniform-green-bound-of-regional-bounds` | `Manhattan.Frozen.Operator.uniform_green_bound_of_regional_bounds` | `Manhattan/Frozen/Operator/UniformGreenBoundOfRegionalBounds.lean` | proved |
| `manuscript.tex:1179-1191` / `est-coefficient-degree-erase` | `Manhattan.Frozen.Estimates.coefficientDegree_erase` | `Manhattan/Frozen/Estimates/CoefficientDegreeErase.lean` | proved |
| `manuscript.tex:1030-1055` / `est-correction-v-euler` | `Manhattan.Frozen.Estimates.correctionV_euler` | `Manhattan/Frozen/Estimates/CorrectionVEuler.lean` | proved |
| `manuscript.tex:743-756` / `est-dispersion-le-half-mul-sq` | `Manhattan.Frozen.Estimates.dispersion_le_half_mul_sq` | `Manhattan/Frozen/Estimates/DispersionLeHalfMulSq.lean` | proved |
| `manuscript.tex:743-756` / `est-dispersion-nonneg` | `Manhattan.Frozen.Estimates.dispersion_nonneg` | `Manhattan/Frozen/Estimates/DispersionNonneg.lean` | proved |
| `manuscript.tex:743-756` / `est-dispersion-quadratic-bounds` | `Manhattan.Frozen.Estimates.dispersion_quadratic_bounds` | `Manhattan/Frozen/Estimates/DispersionQuadraticBounds.lean` | proved |
| `manuscript.tex:1257-1271` / `est-four-estimate-core-le-multiplier` | `Manhattan.Frozen.Estimates.fourEstimateCore_le_multiplier` | `Manhattan/Frozen/Estimates/FourEstimateCoreLeMultiplier.lean` | proved |
| `manuscript.tex:743-758` / `est-h-weight-pos` | `Manhattan.Frozen.Estimates.hWeight_pos` | `Manhattan/Frozen/Estimates/HWeightPos.lean` | proved |
| `manuscript.tex:1121-1125` / `est-log-scale-integral` | `Manhattan.Frozen.Estimates.logScaleIntegral` | `Manhattan/Frozen/Estimates/LogScaleIntegral.lean` | proved |
| `manuscript.tex:1121-1125` / `est-log-scale-integral-le` | `Manhattan.Frozen.Estimates.logScaleIntegral_le` | `Manhattan/Frozen/Estimates/LogScaleIntegralLe.lean` | proved |
| `manuscript.tex:937-944` / `est-mixed-denominator-pos` | `Manhattan.Frozen.Estimates.mixed_denominator_pos` | `Manhattan/Frozen/Estimates/MixedDenominatorPos.lean` | proved |
| `manuscript.tex:937-940` / `est-mixed-residual-eq-indicator` | `Manhattan.Frozen.Estimates.mixedResidual_eq_indicator` | `Manhattan/Frozen/Estimates/MixedResidualEqIndicator.lean` | proved |
| `manuscript.tex:991-1000` / `est-multiplier-comparison-claim-proved` | `Manhattan.Frozen.Estimates.multiplierComparisonClaim_proved` | `Manhattan/Frozen/Estimates/MultiplierComparisonClaimProved.lean` | proved |
| `manuscript.tex:991-1000` / `est-multiplier-comparison-explicit` | `Manhattan.Frozen.Estimates.multiplier_comparison_explicit` | `Manhattan/Frozen/Estimates/MultiplierComparisonExplicit.lean` | proved |
| `manuscript.tex:982-1000` / `est-multiplier-nonneg` | `Manhattan.Frozen.Estimates.multiplier_nonneg` | `Manhattan/Frozen/Estimates/MultiplierNonneg.lean` | proved |
| `manuscript.tex:1352-1355` / `est-one-sub-sigma-mul-correction-v` | `Manhattan.Frozen.Estimates.one_sub_sigma_mul_correctionV` | `Manhattan/Frozen/Estimates/OneSubSigmaMulCorrectionV.lean` | proved |
| `manuscript.tex:1179-1191` / `est-raising-formula-finset` | `Manhattan.Frozen.Estimates.raising_formula_finset` | `Manhattan/Frozen/Estimates/RaisingFormulaFinset.lean` | proved |
| `manuscript.tex:907-958` / `est-sin-ne-zero-on-support` | `Manhattan.Frozen.Estimates.sin_ne_zero_on_support` | `Manhattan/Frozen/Estimates/SinNeZeroOnSupport.lean` | proved |
| `manuscript.tex:1257-1269` / `est-sine-sq-div-sqrt-le` | `Manhattan.Frozen.Estimates.sine_sq_div_sqrt_le` | `Manhattan/Frozen/Estimates/SineSqDivSqrtLe.lean` | proved |
| `manuscript.tex:743-756` / `est-theta-nonneg` | `Manhattan.Frozen.Estimates.theta_nonneg` | `Manhattan/Frozen/Estimates/ThetaNonneg.lean` | proved |
| `manuscript.tex:523-524` / `est-torus-integral-one` | `Manhattan.Frozen.Estimates.torusIntegral_one` | `Manhattan/Frozen/Estimates/TorusIntegralOne.lean` | proved |
| `manuscript.tex:1188-1190` / `est-total-frequency-multiplier-apply` | `Manhattan.Frozen.Estimates.totalFrequencyMultiplier_apply` | `Manhattan/Frozen/Estimates/TotalFrequencyMultiplierApply.lean` | proved |
| `manuscript.tex:192-198` / `thm-main` | `Manhattan.Frozen.Main.theorem_1_1` | `Manhattan/Frozen/Main/Theorem11.lean` | sealed (proved by `Manhattan.Glue.theorem_1_1_proved_of_exists`; awaiting the second reading for the main theorems) |
| `manuscript.tex:576-597` / `prop-generator` | `Manhattan.Frozen.Operator.proposition_generator` | `Manhattan/Frozen/Operator/PropositionGenerator.lean` | proved (retired; superseded by `prop-generator-v2`) |
| `manuscript.tex:555-607` / `prop-generator-v2` | `Manhattan.Frozen.Operator.proposition_generator_v2` | `Manhattan/Frozen/Operator/PropositionGeneratorV2.lean` | proved (second reading recorded) |
| `manuscript.tex:644-661` / `prop-frequency` v2 | `Manhattan.Frozen.Estimates.proposition_frequency` | `Manhattan/Frozen/Estimates/PropositionFrequency.lean` | sealed (proved by `Manhattan.Glue.proposition_frequency_v2`; awaiting the second reading for the main theorems) |
| `manuscript.tex:207-214` / `thm-annealed` | `Manhattan.Frozen.Main.theorem_1_2` | `Manhattan/Frozen/Main/Theorem12.lean` | sealed (proved by `Manhattan.Glue.theorem_1_2_proved_of_exists`; awaiting the second reading for the main theorems) |
| `manuscript.tex:207-214` / `thm-annealed-model-interface` | `Manhattan.theorem_1_2` | `Manhattan/Model/Theorem12.lean` | sealed (proved by `Manhattan.Glue.theorem_1_2_proved_of_exists`; awaiting the second reading for the main theorems) |
| `manuscript.tex:907-917` / `lem-onecoin` v2 | `Manhattan.Frozen.Estimates.lemma_one_coin` | `Manhattan/Frozen/Estimates/LemmaOneCoin.lean` | proved (retired; superseded by `lem-onecoin-v3`) |
| `manuscript.tex:907-958` / `lem-onecoin-v3` | `Manhattan.Frozen.Estimates.lemma_one_coin_v3` | `Manhattan/Frozen/Estimates/LemmaOneCoinV3.lean` | proved (second reading recorded) |
| `manuscript.tex:1007-1018` / `prop-key` | `Manhattan.Frozen.Estimates.proposition_key` | `Manhattan/Frozen/Estimates/PropositionKey.lean` | proved |
| `manuscript.tex:1179-1191 (eq:raise = (45) at :1182)` / `lem-raise-concrete-raising` | `Manhattan.Frozen.Glue.lemma_raise_concrete_raising` | `Manhattan/Frozen/Glue/LemmaRaiseConcreteRaising.lean` | sealed (Lemma 5.1, raising side; awaiting the second reading) |
| `manuscript.tex:1179-1191` / `lem-raise-concrete-adjoint` | `Manhattan.Frozen.Glue.lemma_raise_concrete_adjoint` | `Manhattan/Frozen/Glue/LemmaRaiseConcreteAdjoint.lean` | sealed (Lemma 5.1, adjoint side; awaiting the second reading) |
| `manuscript.tex:743-751 (eq:Hsym = (20) at :749; eq:P = (19) at :745)` / `eq-hsym-concrete` | `Manhattan.Frozen.Glue.hsym_concrete` | `Manhattan/Frozen/Glue/HsymConcrete.lean` | sealed ((Hsym) concrete; awaiting the second reading) |
| `manuscript.tex:1200-1207 (eq:four = (47) at :1203)` / `lem-four-concrete-raising-energy` | `Manhattan.Frozen.Glue.lemma_four_concrete_raising_energy` | `Manhattan/Frozen/Glue/LemmaFourConcreteRaisingEnergy.lean` | sealed (Lemma 5.2, operator half; awaiting the second reading) |
| `manuscript.tex:1200-1207` / `lem-four-concrete-competitor` | `Manhattan.Frozen.Glue.lemma_four_concrete_competitor` | `Manhattan/Frozen/Glue/LemmaFourConcreteCompetitor.lean` | sealed (Lemma 5.2 at the competitor; awaiting the second reading) |
| `manuscript.tex:1212-1221` / `lem-distinct-concrete-frequency` | `Manhattan.Frozen.Glue.lemma_distinct_concrete_frequency` | `Manhattan/Frozen/Glue/LemmaDistinctConcreteFrequency.lean` | sealed (Lemma 5.3 on the RAW/FREQUENCY side only; the operator-level bridge is open; awaiting the second reading) |
| `manuscript.tex:1305-1400` / `lem-correction-calculation-concrete` | `Manhattan.Frozen.Glue.lemma_correction_calculation_concrete` | `Manhattan/Frozen/Glue/LemmaCorrectionCalculationConcrete.lean` | sealed (Lemma 5.4 for the raw mixed residual; awaiting the second reading) |
| `manuscript.tex:765-772 (eq:E = (22))` / `eq-e-summand-one` | `Manhattan.Frozen.Glue.summand_one_bound` | `Manhattan/Frozen/Glue/SummandOne.lean` | sealed (summand 1 of (22); awaiting the second reading) |
| `manuscript.tex:765-772 (eq:E = (22))` / `eq-e-summand-two` | `Manhattan.Frozen.Glue.summand_two_bound` | `Manhattan/Frozen/Glue/SummandTwo.lean` | sealed (summand 2 of (22); awaiting the second reading) |
| `manuscript.tex:765-772 (eq:E = (22))` / `eq-e-summand-three` | `Manhattan.Frozen.Glue.summand_three_bound` | `Manhattan/Frozen/Glue/SummandThree.lean` | sealed (summand 3 of (22); awaiting the second reading) |
| `manuscript.tex:765-772 (eq:E = (22))` / `eq-e-summand-four` | `Manhattan.Frozen.Glue.summand_four_bound` | `Manhattan/Frozen/Glue/SummandFour.lean` | sealed (summand 4 of (22); awaiting the second reading) |
| `manuscript.tex:785-790 (third display of eq:construction = (25))` / `eq-construction-sector-energy` | `Manhattan.Frozen.Glue.sector_energy_bound` | `Manhattan/Frozen/Glue/SectorEnergyBound.lean` | sealed (the repository's "(23)", E_p(f_p,k_p) <= C sqrt(L); awaiting the second reading) |

## Unfrozen public audit and assembly support

These declarations are public support rather than additional frozen paper
anchors. They are listed so the obstruction and the final damping-removal
step remain traceable without manufacturing manifest nodes.

| Source | Lean declaration | File | Status |
|---|---|---|---|
| `manuscript.tex:612`, `manuscript.tex:644-660` | `Manhattan.Competitor.not_competitorBoundClaim_of_raw_frequency` | `Manhattan/Competitor/Obstruction.lean` | proved (audit evidence) |
| `manuscript.tex:612`, `manuscript.tex:644-660` | `Manhattan.Competitor.not_proposition_frequency` | `Manhattan/Competitor/Obstruction.lean` | proved (audit evidence) |
| `manuscript.tex:668-681` | `Manhattan.Glue.annealedGreenBound_of_uniform_damped` | `Manhattan/Glue/Annealed.lean` | proved (assembly support) |
| `manuscript.tex:640-681` | `Manhattan.Glue.annealedGreenBound_of_regional_identity` | `Manhattan/Glue/Annealed.lean` | proved (assembly support) |
| `manuscript.tex:207-214` | `Manhattan.AnnealedGreenBound` | `Manhattan/Model/Subordination.lean` | definition (assembly interface) |
| `manuscript.tex:576-607` | `Manhattan.Glue.proposition_generator` | `Manhattan/Glue/ConcreteGreen.lean` | proved (historical v1 provider; retired from active audit) |
| `manuscript.tex:555-597` | `Manhattan.Glue.proposition_generator_v2` | `Manhattan/Glue/Fiberwise.lean` | proved (provider; second reading recorded) |
| `manuscript.tex:555-583` | `Manhattan.Glue.concreteJointFiberOperator_eq_directIntegral` | `Manhattan/Glue/Fiberwise.lean` | proved (pointwise-fiber support) |
| `manuscript.tex:576-595` | `Manhattan.Glue.torusFiberGenerator_eq_concreteFiberGenerator_torusFrequency` | `Manhattan/Glue/Fiberwise.lean` | proved (pointwise-fiber support) |
| `manuscript.tex:590-607` | `Manhattan.Glue.concreteGreenIdentity` | `Manhattan/Glue/GreenDensity.lean` | proved (Green-density support) |
| `manuscript.tex:668-681` | `Manhattan.Glue.exists_concreteRegionalIntegralBounds` | `Manhattan/Glue/GreenDensity.lean` | proved (conditional regional assembly) |
| `manuscript.tex:207-214` | `Manhattan.Glue.theorem_1_2_of_proposition_frequency` | `Manhattan/Glue/Assembly.lean` | proved (conditional assembly of the main theorem) |
| `manuscript.tex:192-198` | `Manhattan.Glue.theorem_1_1_of_proposition_frequency` | `Manhattan/Glue/Assembly.lean` | proved (conditional assembly of the main theorem) |
| `manuscript.tex:1068-1090` | `Manhattan.Estimates.denominatorBound_proved` | `Manhattan/Estimates/PropositionFiveTwo.lean` | proved (Proposition 4.2 support) |
| `manuscript.tex:1093-1125` | `Manhattan.Estimates.betaIntegralBound_proved` | `Manhattan/Estimates/PropositionFiveTwo.lean` | proved (Proposition 4.2 support) |
| `manuscript.tex:1007-1125` | `Manhattan.Estimates.propositionFiveTwoClaim_proved` | `Manhattan/Estimates/PropositionFiveTwo.lean` | proved (frozen provider) |
| `manuscript.tex:907-958` | `Manhattan.Estimates.LemmaFourTwoSuccessorClaim` | `Manhattan/Estimates/LemmaFourTwoSuccessor.lean` | definition (approved successor vocabulary) |
| `manuscript.tex:907-958` | `Manhattan.Estimates.lemmaFourTwoSuccessorClaim_proved` | `Manhattan/Estimates/LemmaFourTwoSuccessor.lean` | proved (frozen provider) |
| `manuscript.tex:907-958` | `Manhattan.Estimates.lemmaFourTwoIntegralCertificate_proved` | `Manhattan/Estimates/LemmaFourTwoSuccessor.lean` | proved (v3 integral-finiteness support) |
| `manuscript.tex:907-958` | `Manhattan.Estimates.lemmaFourTwoSuccessorV3Claim_proved` | `Manhattan/Estimates/LemmaFourTwoSuccessor.lean` | proved (v3 frozen provider) |
| `manuscript.tex:668-681` | `Manhattan.Estimates.smallSquare_frequency_integral_le` | `Manhattan/Estimates/Regional.lean` | proved (separate regional estimate) |
| `manuscript.tex:668-681` | `Manhattan.Estimates.squareAnnulus_integral_le` | `Manhattan/Estimates/Regional.lean` | proved (separate regional estimate) |
| `manuscript.tex:668-681` | `Manhattan.Estimates.outerRegion_integral_le` | `Manhattan/Estimates/Regional.lean` | proved (separate regional estimate) |
| `manuscript.tex:668-681` | `Manhattan.Estimates.frequencyRegions_cover` | `Manhattan/Estimates/Regional.lean` | proved (regional cover) |
| `manuscript.tex:668-681` | `Manhattan.Estimates.normalizedFrequencyIntegral_le_region_sum` | `Manhattan/Estimates/Regional.lean` | proved (non-circular regional assembly) |
| `manuscript.tex:668-681` | `Manhattan.Estimates.regionalIntegralBoundsOfFrequencyBound` | `Manhattan/Estimates/Regional.lean` | definition (regional certificate constructor) |

## Two texts, and which statements survive (2026-09-05)

The rows above cite `paper/manuscript.tex`, which is the **3 September**
manuscript, hash `b212a597…`, the same file the manifest `source_pin` names.
That text predates the Version 4 rewrite. The current manuscript is beside it
as `paper/manuscript-current.tex`, hash `5bd26a11…`, and it is the version the
authors are editing.

The pin is deliberately left alone. It and every `source:` line range in the
manifest agree with the file they name, so the frozen surface stays internally
consistent and no certified statement has to move. What follows is the
correspondence to the current text, computed by anchoring on `\label` names
rather than on line numbers, which do not survive a rewrite.

**64 of the 76 frozen nodes** anchor on statements that are still in the paper.
The remaining **12** anchor only on statements the rewrite removed:

| Node | Pinned lines | Anchors removed from the current paper |
| --- | --- | --- |
| `est-multiplier-comparison-claim-proved` | 991-1000 | `eq:Mcomp` |
| `est-multiplier-comparison-explicit` | 991-1000 | `eq:Mcomp` |
| `est-one-sub-sigma-mul-correction-v` | 1352-1355 | `eq:onI` |
| `est-sin-ne-zero-on-support` | 907-958 | `lem:onecoin` |
| `lem-onecoin` | 907-917 | `lem:onecoin` |
| `lem-onecoin-v3` | 907-958 | `lem:onecoin` |
| `prop-key` | 1007-1018 | `prop:key`, `eq:key` |
| `lem-four-concrete-raising-energy` | 1200-1207 | `lem:four`, `eq:four` |
| `lem-four-concrete-competitor` | 1200-1207 | `lem:four`, `eq:four` |
| `lem-distinct-concrete-frequency` | 1212-1221 | `lem:distinct`, `eq:distinct` |
| `lem-correction-calculation-concrete` | 1305-1400 | `lem:correction-calculation`, `eq:kenergy`, `eq:err`, `eq:onI`, `eq:support`, `eq:sigmalow`, `eq:ebound` |
| `eq-construction-sector-energy` | 785-790 | `eq:construction` |

These twelve are not stale in the sense of being wrong. They are proved, they
carry only the three standard axioms, and they are part of the frozen route to
`Manhattan.Frozen.Main.theorem_1_1`. What they certify is the decomposition the
paper used before the rewrite: a single key proposition, a degree-four lemma, a
one-sign lemma, a distinctness lemma and an explicit correction calculation.
The current paper reaches the same theorem through the parity construction, the
even majorant and the effective weight, and that route is certified separately
by `Manhattan.V4.theorem_1_1_v4`.

So both routes are live and both are complete; only one of them is the one now
printed. Re-pinning the manifest to the current text would mean re-deriving the
frozen surface against the Version 4 argument, which is a re-certification and
not a correction, and it is not attempted here.
