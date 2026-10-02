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
- Status is `definition` for a frozen definition and `proved` for a frozen
  statement whose axiom closure is exactly the three standard axioms. A row
  marked `superseded` is a proved statement that `Manhattan.Frozen` does not
  import; it names the manifest node (`superseded_by`) used in its place.
- `paper/manuscript.tex` states exactly what the frozen statements state.
  Where it differs from the arXiv version, the difference is recorded in
  [`paper/CHANGES_FROM_ARXIV.md`](paper/CHANGES_FROM_ARXIV.md).

## Main results

The main results are additionally exposed, stated in full, in
[`Manhattan/MainTheorems.lean`](Manhattan/MainTheorems.lean), and both are
restated over a Mathlib-only vocabulary for the comparator (see
[`ManhattanAudit/`](ManhattanAudit/)).

| Source | Main theorem | Certified statement | Comparator |
|---|---|---|---|
| Theorem 1.1, `thm:main`, `manuscript.tex:192-198` | `Manhattan.transience` | `Manhattan.Frozen.Main.theorem_1_1` | `ManhattanAudit/Transience/` |
| Theorem 1.2, `thm:annealed`, `manuscript.tex:207-214` | `Manhattan.annealed_green_bound` | `Manhattan.Frozen.Main.theorem_1_2` | `ManhattanAudit/AnnealedGreenBound/` |

`Manhattan.annealed_green_bound` displays the body of the definition
`Manhattan.AnnealedGreenBound`, which is the type of
`Manhattan.Frozen.Main.theorem_1_2`.

## The frozen surface

The table below is the complete frozen surface; counts and states are checked
against `ledger/manifest.yaml`. That manifest has **76 nodes, all in state
`PROVED`**; each has exactly one row below. A second, independent reading of the
frozen statements is recorded for part of the surface. It is not recorded for the
twelve concrete-lemma rows (`lem-raise-concrete-raising` to
`eq-construction-sector-energy`, the rows of `Manhattan/Frozen/Glue/`) or for the
four rows `thm-main`, `thm-annealed`, `thm-annealed-model-interface` and
`prop-frequency`; the two main theorems are in addition checked by the
comparator challenges under [`ManhattanAudit/`](ManhattanAudit/).

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
| `manuscript.tex:640-666` / `op-frequency-resolvent-le-of-competitor` | `Manhattan.Frozen.Operator.frequency_resolvent_le_of_competitor` | `Manhattan/Frozen/Operator/FrequencyResolventLeOfCompetitor.lean` | proved (superseded by `op-frequency-resolvent-le-of-competitor-v2`) |
| `manuscript.tex:640-666` / `op-frequency-resolvent-le-of-competitor-v2` | `Manhattan.Frozen.Operator.frequency_resolvent_le_of_competitor_v2` | `Manhattan/Frozen/Operator/FrequencyResolventLeOfCompetitorV2.lean` | proved |
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
| `manuscript.tex:192-198` / `thm-main` | `Manhattan.Frozen.Main.theorem_1_1` | `Manhattan/Frozen/Main/Theorem11.lean` | proved (by `Manhattan.Glue.theorem_1_1_proved_of_exists`) |
| `manuscript.tex:576-597` / `prop-generator` | `Manhattan.Frozen.Operator.proposition_generator` | `Manhattan/Frozen/Operator/PropositionGenerator.lean` | proved (superseded by `prop-generator-v2`) |
| `manuscript.tex:555-607` / `prop-generator-v2` | `Manhattan.Frozen.Operator.proposition_generator_v2` | `Manhattan/Frozen/Operator/PropositionGeneratorV2.lean` | proved |
| `manuscript.tex:644-661` / `prop-frequency` | `Manhattan.Frozen.Estimates.proposition_frequency` | `Manhattan/Frozen/Estimates/PropositionFrequency.lean` | proved (by `Manhattan.Glue.proposition_frequency_v2`) |
| `manuscript.tex:207-214` / `thm-annealed` | `Manhattan.Frozen.Main.theorem_1_2` | `Manhattan/Frozen/Main/Theorem12.lean` | proved (by `Manhattan.Glue.theorem_1_2_proved_of_exists`) |
| `manuscript.tex:207-214` / `thm-annealed-model-interface` | `Manhattan.theorem_1_2` | `Manhattan/Model/Theorem12.lean` | proved (by `Manhattan.Glue.theorem_1_2_proved_of_exists`) |
| `manuscript.tex:907-917` / `lem-onecoin` | `Manhattan.Frozen.Estimates.lemma_one_coin` | `Manhattan/Frozen/Estimates/LemmaOneCoin.lean` | proved (superseded by `lem-onecoin-v3`) |
| `manuscript.tex:907-958` / `lem-onecoin-v3` | `Manhattan.Frozen.Estimates.lemma_one_coin_v3` | `Manhattan/Frozen/Estimates/LemmaOneCoinV3.lean` | proved |
| `manuscript.tex:1007-1018` / `prop-key` | `Manhattan.Frozen.Estimates.proposition_key` | `Manhattan/Frozen/Estimates/PropositionKey.lean` | proved |
| `manuscript.tex:1179-1191 (eq:raise = (45) at :1182)` / `lem-raise-concrete-raising` | `Manhattan.Frozen.Glue.lemma_raise_concrete_raising` | `Manhattan/Frozen/Glue/LemmaRaiseConcreteRaising.lean` | proved (Lemma 5.1, raising side) |
| `manuscript.tex:1179-1191` / `lem-raise-concrete-adjoint` | `Manhattan.Frozen.Glue.lemma_raise_concrete_adjoint` | `Manhattan/Frozen/Glue/LemmaRaiseConcreteAdjoint.lean` | proved (Lemma 5.1, adjoint side) |
| `manuscript.tex:743-751 (eq:Hsym = (20) at :749; eq:P = (19) at :745)` / `eq-hsym-concrete` | `Manhattan.Frozen.Glue.hsym_concrete` | `Manhattan/Frozen/Glue/HsymConcrete.lean` | proved ((Hsym) concrete) |
| `manuscript.tex:1200-1207 (eq:four = (47) at :1203)` / `lem-four-concrete-raising-energy` | `Manhattan.Frozen.Glue.lemma_four_concrete_raising_energy` | `Manhattan/Frozen/Glue/LemmaFourConcreteRaisingEnergy.lean` | proved (Lemma 5.2, operator half) |
| `manuscript.tex:1200-1207` / `lem-four-concrete-competitor` | `Manhattan.Frozen.Glue.lemma_four_concrete_competitor` | `Manhattan/Frozen/Glue/LemmaFourConcreteCompetitor.lean` | proved (Lemma 5.2 at the competitor) |
| `manuscript.tex:1212-1221` / `lem-distinct-concrete-frequency` | `Manhattan.Frozen.Glue.lemma_distinct_concrete_frequency` | `Manhattan/Frozen/Glue/LemmaDistinctConcreteFrequency.lean` | proved (Lemma 5.3, raw frequency side only) |
| `manuscript.tex:1305-1400` / `lem-correction-calculation-concrete` | `Manhattan.Frozen.Glue.lemma_correction_calculation_concrete` | `Manhattan/Frozen/Glue/LemmaCorrectionCalculationConcrete.lean` | proved (Lemma 5.4, raw mixed residual) |
| `manuscript.tex:765-772 (eq:E = (22))` / `eq-e-summand-one` | `Manhattan.Frozen.Glue.summand_one_bound` | `Manhattan/Frozen/Glue/SummandOne.lean` | proved (summand 1 of (22)) |
| `manuscript.tex:765-772 (eq:E = (22))` / `eq-e-summand-two` | `Manhattan.Frozen.Glue.summand_two_bound` | `Manhattan/Frozen/Glue/SummandTwo.lean` | proved (summand 2 of (22)) |
| `manuscript.tex:765-772 (eq:E = (22))` / `eq-e-summand-three` | `Manhattan.Frozen.Glue.summand_three_bound` | `Manhattan/Frozen/Glue/SummandThree.lean` | proved (summand 3 of (22)) |
| `manuscript.tex:765-772 (eq:E = (22))` / `eq-e-summand-four` | `Manhattan.Frozen.Glue.summand_four_bound` | `Manhattan/Frozen/Glue/SummandFour.lean` | proved (summand 4 of (22)) |
| `manuscript.tex:785-790 (third display of eq:construction = (25))` / `eq-construction-sector-energy` | `Manhattan.Frozen.Glue.sector_energy_bound` | `Manhattan/Frozen/Glue/SectorEnergyBound.lean` | proved (the repository's "(23)", E_p(f_p,k_p) <= C sqrt(L)) |

## Unfrozen public audit and assembly support

These declarations are public support rather than additional frozen paper
anchors. They are listed so that the obstruction and the damping-removal step
are traceable.

| Source | Lean declaration | File | Status |
|---|---|---|---|
| `manuscript.tex:612`, `manuscript.tex:644-660` | `Manhattan.Competitor.not_competitorBoundClaim_of_raw_frequency` | `Manhattan/Competitor/Obstruction.lean` | proved (audit evidence) |
| `manuscript.tex:612`, `manuscript.tex:644-660` | `Manhattan.Competitor.not_proposition_frequency` | `Manhattan/Competitor/Obstruction.lean` | proved (audit evidence) |
| `manuscript.tex:668-681` | `Manhattan.Glue.annealedGreenBound_of_uniform_damped` | `Manhattan/Glue/Annealed.lean` | proved (assembly support) |
| `manuscript.tex:640-681` | `Manhattan.Glue.annealedGreenBound_of_regional_identity` | `Manhattan/Glue/Annealed.lean` | proved (assembly support) |
| `manuscript.tex:207-214` | `Manhattan.AnnealedGreenBound` | `Manhattan/Model/Subordination.lean` | definition (assembly interface) |
| `manuscript.tex:576-607` | `Manhattan.Glue.proposition_generator` | `Manhattan/Glue/ConcreteGreen.lean` | proved (provider of the superseded node `prop-generator`) |
| `manuscript.tex:555-597` | `Manhattan.Glue.proposition_generator_v2` | `Manhattan/Glue/Fiberwise.lean` | proved (provider of `prop-generator-v2`) |
| `manuscript.tex:555-583` | `Manhattan.Glue.concreteJointFiberOperator_eq_directIntegral` | `Manhattan/Glue/Fiberwise.lean` | proved (pointwise-fiber support) |
| `manuscript.tex:576-595` | `Manhattan.Glue.torusFiberGenerator_eq_concreteFiberGenerator_torusFrequency` | `Manhattan/Glue/Fiberwise.lean` | proved (pointwise-fiber support) |
| `manuscript.tex:590-607` | `Manhattan.Glue.concreteGreenIdentity` | `Manhattan/Glue/GreenDensity.lean` | proved (Green-density support) |
| `manuscript.tex:668-681` | `Manhattan.Glue.exists_concreteRegionalIntegralBounds` | `Manhattan/Glue/GreenDensity.lean` | proved (conditional regional assembly) |
| `manuscript.tex:207-214` | `Manhattan.Glue.theorem_1_2_of_proposition_frequency` | `Manhattan/Glue/Assembly.lean` | proved (conditional assembly of the main theorem) |
| `manuscript.tex:192-198` | `Manhattan.Glue.theorem_1_1_of_proposition_frequency` | `Manhattan/Glue/Assembly.lean` | proved (conditional assembly of the main theorem) |
| `manuscript.tex:1068-1090` | `Manhattan.Estimates.denominatorBound_proved` | `Manhattan/Estimates/PropositionFiveTwo.lean` | proved (Proposition 4.2 support) |
| `manuscript.tex:1093-1125` | `Manhattan.Estimates.betaIntegralBound_proved` | `Manhattan/Estimates/PropositionFiveTwo.lean` | proved (Proposition 4.2 support) |
| `manuscript.tex:1007-1125` | `Manhattan.Estimates.propositionFiveTwoClaim_proved` | `Manhattan/Estimates/PropositionFiveTwo.lean` | proved (provider of `prop-key`) |
| `manuscript.tex:907-958` | `Manhattan.Estimates.LemmaFourTwoSuccessorClaim` | `Manhattan/Estimates/LemmaFourTwoSuccessor.lean` | definition (claim vocabulary of `lem-onecoin`) |
| `manuscript.tex:907-958` | `Manhattan.Estimates.lemmaFourTwoSuccessorClaim_proved` | `Manhattan/Estimates/LemmaFourTwoSuccessor.lean` | proved (provider of `lem-onecoin`) |
| `manuscript.tex:907-958` | `Manhattan.Estimates.lemmaFourTwoIntegralCertificate_proved` | `Manhattan/Estimates/LemmaFourTwoSuccessor.lean` | proved (integral-finiteness support) |
| `manuscript.tex:907-958` | `Manhattan.Estimates.lemmaFourTwoSuccessorV3Claim_proved` | `Manhattan/Estimates/LemmaFourTwoSuccessor.lean` | proved (provider of `lem-onecoin-v3`) |
| `manuscript.tex:668-681` | `Manhattan.Estimates.smallSquare_frequency_integral_le` | `Manhattan/Estimates/Regional.lean` | proved (separate regional estimate) |
| `manuscript.tex:668-681` | `Manhattan.Estimates.squareAnnulus_integral_le` | `Manhattan/Estimates/Regional.lean` | proved (separate regional estimate) |
| `manuscript.tex:668-681` | `Manhattan.Estimates.outerRegion_integral_le` | `Manhattan/Estimates/Regional.lean` | proved (separate regional estimate) |
| `manuscript.tex:668-681` | `Manhattan.Estimates.frequencyRegions_cover` | `Manhattan/Estimates/Regional.lean` | proved (regional cover) |
| `manuscript.tex:668-681` | `Manhattan.Estimates.normalizedFrequencyIntegral_le_region_sum` | `Manhattan/Estimates/Regional.lean` | proved (non-circular regional assembly) |
| `manuscript.tex:668-681` | `Manhattan.Estimates.regionalIntegralBoundsOfFrequencyBound` | `Manhattan/Estimates/Regional.lean` | definition (regional certificate constructor) |

## The arXiv version, and which statements it prints

The rows above cite `paper/manuscript.tex`, the file the manifest
`source_pin` names.  The arXiv version, arXiv:2609.07621v1, has a different proof
of the frequency bound; its unmodified source
is `paper/arxiv/main.tex`, and
[`paper/CHANGES_FROM_ARXIV.md`](paper/CHANGES_FROM_ARXIV.md) compares the two
texts.

The pin and every `source:` line range in the manifest agree with the file
they name, so the frozen surface stays internally consistent.  What follows is
the correspondence to the arXiv text, computed by anchoring on `\label` names
rather than on line numbers.

**64 of the 76 frozen nodes** anchor on statements that the arXiv text also
prints.  The remaining **12** anchor only on statements it does not print:

| Node | Pinned lines | Anchors absent from the arXiv text |
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

These twelve are proved, they
carry only the three standard axioms, and they are part of the frozen route to
`Manhattan.Frozen.Main.theorem_1_1`. What they certify is the decomposition of
`paper/manuscript.tex`: a single key proposition, a degree-four lemma, a
one-sign lemma, a distinctness lemma and an explicit correction calculation.
The arXiv text reaches the same theorem through the parity construction, the
even majorant and the effective weight, and that route is certified separately
by `Manhattan.V4.theorem_1_1_v4`.

So both routes are complete: the frozen surface is pinned to
`paper/manuscript.tex`, and the arXiv argument is certified separately.
