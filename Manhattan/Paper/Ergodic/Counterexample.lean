import Manhattan.Paper.Ergodic.Law
import Manhattan.Paper.Ergodic.Recurrence

/-!
# The remark: stationary, ergodic and fair does not imply transient

This file assembles the remark of the manuscript preceding
`\begin{problem}[Which orientations are transient]`. The law `ergodicLaw` is
stationary for the whole `ℤ²` translation action, ergodic for it, and has fair
one-point marginals, and yet almost every realization has a divergent Green
series, that is, is recurrent.

The only unproved input is `SimpleRandomWalkRecurrent`, Pólya's theorem in two
dimensions; everything else, including the reduction of the alternating walk to
the simple random walk at even times, is proved in this directory.

Paper: the remark before `\begin{problem}[Which orientations are transient]`.
-/

namespace Manhattan.Paper.Ergodic

open MeasureTheory ProbabilityTheory
open scoped ENNReal symmDiff

set_option maxRecDepth 4000

/-! ### Numerical witnesses

These evaluate the counts of the reduction, so the statements below are not
about empty sets of paths. -/

/-- Four of the sixteen two-step simple-random-walk paths are loops. -/
theorem srwCount_two : srwCount 2 0 = 4 := by decide

/-- The `36 = binom(4,2)^2` four-step loops of the simple random walk. -/
theorem srwCount_four : srwCount 4 0 = 36 := by decide

/-- The alternating walk cannot return in two steps. -/
theorem pathCount_altBase_two : pathCount altBase 2 0 0 = 0 := by decide

/-- Two of the sixteen four-letter words return the alternating walk to the
origin, and `2 * 2 = 4 = srwCount 2 0` as `two_mul_pathCount` asserts. -/
theorem pathCount_altBase_four : pathCount altBase 4 0 0 = 2 := by decide

/-- The reflected environment has the same return counts. -/
theorem pathCount_altEnv_four : pathCount (altEnv (.negative, .positive)) 4 0 0 = 2 := by
  decide

/-! ### Almost every realization -/

theorem measurableSet_range_altEnv : MeasurableSet (Set.range altEnv) := by
  rw [show Set.range altEnv = ⋃ uv : Orientation × Orientation, ({altEnv uv} : Set Environment) by
      ext ω; simp]
  exact MeasurableSet.iUnion fun uv => measurableSet_singleton _

theorem ergodicLaw_compl_range : ergodicLaw (Set.range altEnv)ᶜ = 0 := by
  rw [measure_compl measurableSet_range_altEnv (measure_ne_top _ _), measure_univ,
    ergodicLaw_range, tsub_self]

/-- Every realization is a translate of the alternating environment. -/
theorem ae_eq_translate_altBase :
    ∀ᵐ ω ∂ergodicLaw, ∃ x : Site, ω = translateEnvironment x altBase := by
  rw [MeasureTheory.ae_iff]
  refine measure_mono_null (fun ω hω => ?_) ergodicLaw_compl_range
  simp only [Set.mem_setOf_eq, not_exists] at hω
  simp only [Set.mem_compl_iff, Set.mem_range, not_exists]
  intro uv huv
  exact hω (transitionSite (.positive, .positive) uv)
    (huv ▸ altEnv_eq_translate_base uv)

/-- Almost every realization is recurrent. -/
theorem ae_discreteGreen_eq_top (h : SimpleRandomWalkRecurrent) :
    ∀ᵐ ω ∂ergodicLaw, discreteGreen ω 0 = ⊤ := by
  rw [MeasureTheory.ae_iff]
  refine measure_mono_null (fun ω hω => ?_) ergodicLaw_compl_range
  simp only [Set.mem_setOf_eq] at hω
  simp only [Set.mem_compl_iff, Set.mem_range, not_exists]
  intro uv huv
  exact hω (huv ▸ discreteGreen_altEnv_eq_top h uv)

/-! ### The counterexample law is not the product law -/

/-- Under the counterexample law the two horizontal signs at heights `0` and `1`
are always opposite. -/
theorem ergodicLaw_two_lines :
    ergodicLaw {ω : Environment | ω (.horizontal, 0) = .positive ∧
      ω (.horizontal, 1) = .positive} = 0 := by
  classical
  rw [ergodicLaw_apply, sum_signPair]
  simp only [Set.indicator_apply, Set.mem_setOf_eq, altEnv_horizontal, parityShift_zero,
    parityShift_one, flipOrientation, and_false, false_and, if_false, reduceCtorEq]
  simp

/-- Under the product law of the paper they are independent, so that event has
probability `1/4`. -/
theorem environmentLaw_two_lines :
    environmentLaw {ω : Environment | ω (.horizontal, 0) = .positive ∧
      ω (.horizontal, 1) = .positive} = 4⁻¹ := by
  have hindep : IndepFun (fun ω : Environment => ω (.horizontal, 0))
      (fun ω : Environment => ω (.horizontal, 1)) environmentLaw :=
    iIndepFun_orientation.indepFun (by decide)
  have hset : {ω : Environment | ω (.horizontal, 0) = .positive ∧
      ω (.horizontal, 1) = .positive} =
      ((fun ω : Environment => ω (.horizontal, 0)) ⁻¹' {Orientation.positive}) ∩
        ((fun ω : Environment => ω (.horizontal, 1)) ⁻¹' {Orientation.positive}) := rfl
  have hmarg : ∀ l : LineIndex,
      environmentLaw ((fun ω : Environment => ω l) ⁻¹' {Orientation.positive}) = 2⁻¹ := by
    intro l
    rw [← Measure.map_apply (measurable_pi_apply l) (measurableSet_singleton _),
      (measurePreserving_orientation l).map_eq, fairCoin,
      PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), fairCoinPMF,
      PMF.uniformOfFintype_apply, show Fintype.card Orientation = 2 from rfl]
    norm_num
  rw [hset, hindep.measure_inter_preimage_eq_mul _ _ (measurableSet_singleton _)
    (measurableSet_singleton _), hmarg, hmarg]
  rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num,
    ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]

/-- The counterexample law is a different measure from the product law of
Theorem 1.1. -/
theorem ergodicLaw_ne_environmentLaw : ergodicLaw ≠ environmentLaw := by
  intro h
  have := ergodicLaw_two_lines
  rw [h, environmentLaw_two_lines] at this
  exact absurd this (by norm_num)

/-! ### The remark -/

/-- **The remark of the manuscript.** Stationarity under the full `ℤ²`
translation action, ergodicity for that action and fair one-point marginals do
not imply transience: the uniform law on the four alternating environments has
all three properties, and almost every realization has a divergent Green series.

The one hypothesis is recurrence of the two-dimensional simple random walk. -/
theorem stationary_ergodic_fair_not_transient (h : SimpleRandomWalkRecurrent) :
    IsProbabilityMeasure ergodicLaw ∧
    (∀ x : Site, MeasurePreserving (translateEnvironment x) ergodicLaw ergodicLaw) ∧
    (∀ s : Set Environment,
      (∀ x : Site, ergodicLaw (s ∆ (translateEnvironment x ⁻¹' s)) = 0) →
        ergodicLaw s = 0 ∨ ergodicLaw s = 1) ∧
    (∀ (l : LineIndex) (o : Orientation),
      ergodicLaw {ω : Environment | ω l = o} = (2 : ℝ≥0∞)⁻¹) ∧
    (∀ᵐ ω ∂ergodicLaw, ∃ x : Site, ω = translateEnvironment x altBase) ∧
    (∀ᵐ ω ∂ergodicLaw, discreteGreen ω 0 = ⊤) :=
  ⟨inferInstance, measurePreserving_translate, ergodicLaw_eq_zero_or_one_of_ae_invariant,
    ergodicLaw_marginal, ae_eq_translate_altBase, ae_discreteGreen_eq_top h⟩

/-! ### Axiom audit -/

#print axioms stationary_ergodic_fair_not_transient
#print axioms two_step
#print axioms two_mul_pathCount
#print axioms blockReturn_add_neg
#print axioms discreteGreen_altEnv_eq_top
#print axioms measurePreserving_translate
#print axioms ergodicLaw_eq_zero_or_one_of_ae_invariant
#print axioms ergodicLaw_marginal
#print axioms ergodicLaw_singleton
#print axioms ncard_range_altEnv
#print axioms translate_transitive
#print axioms ergodicLaw_ne_environmentLaw
#print axioms not_ergodic_even_sublattice

end Manhattan.Paper.Ergodic
