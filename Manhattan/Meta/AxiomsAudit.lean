import Manhattan.Frozen.Operator.DampedOrbitHasDerivAt
import Manhattan.Frozen.Operator.DampedOrbitNormLe
import Manhattan.Frozen.Operator.FiberAEqFormula
import Manhattan.Frozen.Operator.FiberANormLe
import Manhattan.Frozen.Operator.FiberASkewAdjoint
import Manhattan.Frozen.Operator.FiberSEqFormula
import Manhattan.Frozen.Operator.FiberSNonpositive
import Manhattan.Frozen.Operator.FiberSNormLe
import Manhattan.Frozen.Operator.FiberSSelfAdjoint
import Manhattan.Frozen.Operator.FrequencyResolventLeOfCompetitorV2
import Manhattan.Frozen.Operator.GeneratorCommutesOperatorSemigroup
import Manhattan.Frozen.Operator.HBijective
import Manhattan.Frozen.Operator.IntegrableOnDampedOrbit
import Manhattan.Frozen.Operator.IntegrableOnResolventDampedOrbit
import Manhattan.Frozen.Operator.IntegralInnerOperatorSemigroupEqResolvent
import Manhattan.Frozen.Operator.LaplaceVectorResolventOperator
import Manhattan.Frozen.Operator.LogarithmicTailEqTwo
import Manhattan.Frozen.Operator.MinusBijective
import Manhattan.Frozen.Operator.OperatorSemigroupHasDerivAt
import Manhattan.Frozen.Operator.PlusBijective
import Manhattan.Frozen.Operator.PositionFourierNorm
import Manhattan.Frozen.Operator.PositionFourierSingle
import Manhattan.Frozen.Operator.PropositionGeneratorV2
import Manhattan.Frozen.Operator.RealFormHCoercive
import Manhattan.Frozen.Operator.RealFormMinusCoercive
import Manhattan.Frozen.Operator.RealFormPlusCoercive
import Manhattan.Frozen.Operator.ResolventEquivSymmApply
import Manhattan.Frozen.Operator.ResolventOperatorBijective
import Manhattan.Frozen.Operator.ResolventOperatorInjective
import Manhattan.Frozen.Operator.ResolventOperatorLaplaceVector
import Manhattan.Frozen.Operator.ResolventQuadraticLe
import Manhattan.Frozen.Operator.ResolventQuadraticLeHMinusEnergy
import Manhattan.Frozen.Operator.TendstoDampedOrbitAtTop
import Manhattan.Frozen.Operator.UniformGreenBoundOfRegionalBounds
import Manhattan.Frozen.Estimates.CoefficientDegreeErase
import Manhattan.Frozen.Estimates.CorrectionVEuler
import Manhattan.Frozen.Estimates.DispersionLeHalfMulSq
import Manhattan.Frozen.Estimates.DispersionNonneg
import Manhattan.Frozen.Estimates.DispersionQuadraticBounds
import Manhattan.Frozen.Estimates.FourEstimateCoreLeMultiplier
import Manhattan.Frozen.Estimates.HWeightPos
import Manhattan.Frozen.Estimates.LogScaleIntegral
import Manhattan.Frozen.Estimates.LogScaleIntegralLe
import Manhattan.Frozen.Estimates.LemmaOneCoinV3
import Manhattan.Frozen.Estimates.MixedDenominatorPos
import Manhattan.Frozen.Estimates.MixedResidualEqIndicator
import Manhattan.Frozen.Estimates.MultiplierComparisonClaimProved
import Manhattan.Frozen.Estimates.MultiplierComparisonExplicit
import Manhattan.Frozen.Estimates.MultiplierNonneg
import Manhattan.Frozen.Estimates.OneSubSigmaMulCorrectionV
import Manhattan.Frozen.Estimates.PropositionKey
import Manhattan.Frozen.Estimates.RaisingFormulaFinset
import Manhattan.Frozen.Estimates.SinNeZeroOnSupport
import Manhattan.Frozen.Estimates.SineSqDivSqrtLe
import Manhattan.Frozen.Estimates.ThetaNonneg
import Manhattan.Frozen.Estimates.TorusIntegralOne
import Manhattan.Frozen.Estimates.TotalFrequencyMultiplierApply
import Manhattan.Glue.JointFiberization
import Manhattan.Competitor.Obstruction
import Manhattan.Glue.Annealed
import Manhattan.Estimates.LemmaFourTwoSuccessor
import Manhattan.Estimates.Regional
import Manhattan.Glue.Assembly
import Manhattan.Glue.Correction
import Manhattan.Glue.GreenDensity
import Manhattan.Glue.SectorEnergy
import Manhattan.Frozen.Estimates.PropositionFrequency
import Manhattan.Frozen.Glue.LemmaRaiseConcreteRaising
import Manhattan.Frozen.Glue.LemmaRaiseConcreteAdjoint
import Manhattan.Frozen.Glue.HsymConcrete
import Manhattan.Frozen.Glue.LemmaFourConcreteRaisingEnergy
import Manhattan.Frozen.Glue.LemmaFourConcreteCompetitor
import Manhattan.Frozen.Glue.LemmaDistinctConcreteFrequency
import Manhattan.Frozen.Glue.LemmaCorrectionCalculationConcrete
import Manhattan.Frozen.Glue.SummandOne
import Manhattan.Frozen.Glue.SummandTwo
import Manhattan.Frozen.Glue.SummandThree
import Manhattan.Frozen.Glue.SummandFour
import Manhattan.Frozen.Glue.SectorEnergyBound
import Manhattan.Frozen.Main.Theorem12
import Manhattan.V4.Move2Supply
import Manhattan.Frozen.Main.Theorem11

/-!
# Axiom audit

Every active PROVED frozen statement and the sorry-free joint-fiberization
bridge are checked here. Retired historical predecessors are excluded. The
headline cone `theorem_1_1 <- theorem_1_2 <- proposition_frequency (v2) <-
equation (23)` is at the end of the file: none of it may report `sorryAx`.
-/

#print axioms Manhattan.Frozen.Operator.dampedOrbit_hasDerivAt
#print axioms Manhattan.Frozen.Operator.dampedOrbit_norm_le
#print axioms Manhattan.Frozen.Operator.fiberA_eq_formula
#print axioms Manhattan.Frozen.Operator.fiberA_norm_le
#print axioms Manhattan.Frozen.Operator.fiberA_skewAdjoint
#print axioms Manhattan.Frozen.Operator.fiberS_eq_formula
#print axioms Manhattan.Frozen.Operator.fiberS_nonpositive
#print axioms Manhattan.Frozen.Operator.fiberS_norm_le
#print axioms Manhattan.Frozen.Operator.fiberS_selfAdjoint
#print axioms Manhattan.Frozen.Operator.frequency_resolvent_le_of_competitor_v2
#print axioms Manhattan.Frozen.Operator.generator_commutes_operatorSemigroup
#print axioms Manhattan.Frozen.Operator.H_bijective
#print axioms Manhattan.Frozen.Operator.integrableOn_dampedOrbit
#print axioms Manhattan.Frozen.Operator.integrableOn_resolvent_dampedOrbit
#print axioms Manhattan.Frozen.Operator.integral_inner_operatorSemigroup_eq_resolvent
#print axioms Manhattan.Frozen.Operator.laplaceVector_resolventOperator
#print axioms Manhattan.Frozen.Operator.logarithmicTail_eq_two
#print axioms Manhattan.Frozen.Operator.minus_bijective
#print axioms Manhattan.Frozen.Operator.operatorSemigroup_hasDerivAt
#print axioms Manhattan.Frozen.Operator.plus_bijective
#print axioms Manhattan.Frozen.Operator.positionFourier_norm
#print axioms Manhattan.Frozen.Operator.positionFourier_single
#print axioms Manhattan.Frozen.Operator.proposition_generator_v2
#print axioms Manhattan.Frozen.Operator.realForm_H_coercive
#print axioms Manhattan.Frozen.Operator.realForm_minus_coercive
#print axioms Manhattan.Frozen.Operator.realForm_plus_coercive
#print axioms Manhattan.Frozen.Operator.resolventEquiv_symm_apply
#print axioms Manhattan.Frozen.Operator.resolventOperator_bijective
#print axioms Manhattan.Frozen.Operator.resolventOperator_injective
#print axioms Manhattan.Frozen.Operator.resolventOperator_laplaceVector
#print axioms Manhattan.Frozen.Operator.resolventQuadratic_le
#print axioms Manhattan.Frozen.Operator.resolventQuadratic_le_hMinusEnergy
#print axioms Manhattan.Frozen.Operator.tendsto_dampedOrbit_atTop
#print axioms Manhattan.Frozen.Operator.uniform_green_bound_of_regional_bounds
#print axioms Manhattan.Frozen.Estimates.coefficientDegree_erase
#print axioms Manhattan.Frozen.Estimates.correctionV_euler
#print axioms Manhattan.Frozen.Estimates.dispersion_le_half_mul_sq
#print axioms Manhattan.Frozen.Estimates.dispersion_nonneg
#print axioms Manhattan.Frozen.Estimates.dispersion_quadratic_bounds
#print axioms Manhattan.Frozen.Estimates.fourEstimateCore_le_multiplier
#print axioms Manhattan.Frozen.Estimates.hWeight_pos
#print axioms Manhattan.Frozen.Estimates.logScaleIntegral
#print axioms Manhattan.Frozen.Estimates.logScaleIntegral_le
#print axioms Manhattan.Frozen.Estimates.lemma_one_coin_v3
#print axioms Manhattan.Frozen.Estimates.mixed_denominator_pos
#print axioms Manhattan.Frozen.Estimates.mixedResidual_eq_indicator
#print axioms Manhattan.Frozen.Estimates.multiplierComparisonClaim_proved
#print axioms Manhattan.Frozen.Estimates.multiplier_comparison_explicit
#print axioms Manhattan.Frozen.Estimates.multiplier_nonneg
#print axioms Manhattan.Frozen.Estimates.one_sub_sigma_mul_correctionV
#print axioms Manhattan.Frozen.Estimates.proposition_key
#print axioms Manhattan.Frozen.Estimates.raising_formula_finset
#print axioms Manhattan.Frozen.Estimates.sin_ne_zero_on_support
#print axioms Manhattan.Frozen.Estimates.sine_sq_div_sqrt_le
#print axioms Manhattan.Frozen.Estimates.theta_nonneg
#print axioms Manhattan.Frozen.Estimates.torusIntegral_one
#print axioms Manhattan.Frozen.Estimates.totalFrequencyMultiplier_apply
#print axioms Manhattan.Glue.jointGenerator_fiberizes
#print axioms Manhattan.Glue.jointGenerator_eq_transform_symm
#print axioms Manhattan.Competitor.not_competitorBoundClaim_of_raw_frequency
#print axioms Manhattan.Competitor.not_proposition_frequency
#print axioms Manhattan.Glue.annealedGreenBound_of_uniform_damped
#print axioms Manhattan.Glue.annealedGreenBound_of_regional_identity
#print axioms Manhattan.Estimates.denominatorBound_proved
#print axioms Manhattan.Estimates.betaIntegralBound_proved
#print axioms Manhattan.Estimates.propositionFiveTwoClaim_proved
#print axioms Manhattan.Estimates.LemmaFourTwoSuccessorClaim
#print axioms Manhattan.Estimates.lemmaFourTwoSuccessorClaim_proved
#print axioms Manhattan.Estimates.lemmaFourTwoIntegralCertificate_proved
#print axioms Manhattan.Estimates.lemmaFourTwoSuccessorV3Claim_proved
#print axioms Manhattan.Operator.frequency_resolvent_le_of_competitor_v2
#print axioms Manhattan.Estimates.smallSquare_frequency_integral_le
#print axioms Manhattan.Estimates.squareAnnulus_integral_le
#print axioms Manhattan.Estimates.outerRegion_integral_le
#print axioms Manhattan.Estimates.frequencyRegions_cover
#print axioms Manhattan.Estimates.normalizedFrequencyIntegral_le_region_sum
#print axioms Manhattan.Estimates.regionalIntegralBoundsOfFrequencyBound
#print axioms Manhattan.Glue.proposition_generator_v2
#print axioms Manhattan.Glue.torusFiberGenerator_eq_concreteFiberGenerator_torusFrequency
#print axioms Manhattan.Glue.concreteFiberDirectIntegral_coordinate
#print axioms Manhattan.Glue.concreteJointFiberOperator_eq_directIntegral
#print axioms Manhattan.Glue.concreteGreenDensity_measurable
#print axioms Manhattan.Glue.concreteGreenDensity_nonneg
#print axioms Manhattan.Glue.concreteGreenDensity_integrable
#print axioms Manhattan.Glue.concreteGreenIdentity
#print axioms Manhattan.Glue.exists_concreteRegionalIntegralBounds
#print axioms Manhattan.Glue.theorem_1_2_of_proposition_frequency
#print axioms Manhattan.Glue.theorem_1_1_of_proposition_frequency
#print axioms Manhattan.norm_type112DiagonalProjection_le
#print axioms Manhattan.rawCorrectionFunction_memLp
#print axioms Manhattan.correctionWalsh_mem_degree
#print axioms Manhattan.Glue.normalizedObjective_eq
#print axioms Manhattan.Glue.correctedLowDegreeData_cancelsAt
#print axioms Manhattan.Glue.correctedLowDegreeData_exists_horizontal
#print axioms Manhattan.Glue.not_all_frequency_exactCancellation

#print axioms Manhattan.Glue.exists_concreteSectorEnergyBound
#print axioms Manhattan.Glue.proposition_frequency_v2
#print axioms Manhattan.Frozen.Estimates.proposition_frequency
#print axioms Manhattan.theorem_1_2
#print axioms Manhattan.Frozen.Main.theorem_1_2
#print axioms Manhattan.Frozen.Main.theorem_1_1

-- The concrete-lemma anchors sealed (ledger/briefs/the sealing pass.md item 2).
#print axioms Manhattan.Frozen.Glue.lemma_raise_concrete_raising
#print axioms Manhattan.Frozen.Glue.lemma_raise_concrete_adjoint
#print axioms Manhattan.Frozen.Glue.hsym_concrete
#print axioms Manhattan.Frozen.Glue.lemma_four_concrete_raising_energy
#print axioms Manhattan.Frozen.Glue.lemma_four_concrete_competitor
#print axioms Manhattan.Frozen.Glue.lemma_distinct_concrete_frequency
#print axioms Manhattan.Frozen.Glue.lemma_correction_calculation_concrete
#print axioms Manhattan.Frozen.Glue.summand_one_bound
#print axioms Manhattan.Frozen.Glue.summand_two_bound
#print axioms Manhattan.Frozen.Glue.summand_three_bound
#print axioms Manhattan.Frozen.Glue.summand_four_bound
#print axioms Manhattan.Frozen.Glue.sector_energy_bound

-- The Version 4 route to Theorem 1.1 (`Manhattan/V4/`, no manifest node).
#print axioms Manhattan.V4.v4Move2Supply_proved
#print axioms Manhattan.V4.annealedGreenBound_proved
#print axioms Manhattan.V4.theorem_1_1_v4
