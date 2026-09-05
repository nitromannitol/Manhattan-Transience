import Manhattan.Model.Subordination
import Manhattan.Operator.Frequency
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Removing the Laplace damping

The uniform damped estimate implies the undamped annealed Green bound by
Fatou's lemma along `lambda_n = 1 / (n + 1)`. This is the final
measure-theoretic bridge in Theorem 1.2.

Paper: `manuscript.tex:668-681`.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace Manhattan.Glue

/-- A uniform bound for every positive Laplace parameter up to one implies
the full assertion packaged as `AnnealedGreenBound`. -/
theorem annealedGreenBound_of_uniform_damped
    (C : ℝ≥0∞) (hC : C < ∞)
    (hbound : ∀ lambda : ℝ, 0 < lambda → lambda ≤ 1 →
      ∫⁻ t in Ici 0,
        ENNReal.ofReal (Real.exp (-lambda * t)) *
          Manhattan.annealedContinuousKernel t 0 0 ≤ C) :
    Manhattan.AnnealedGreenBound := by
  refine ⟨C, hC, hbound, ?_⟩
  let lambda : ℕ → ℝ := fun n => ((n + 1 : ℕ) : ℝ)⁻¹
  let f : ℕ → ℝ → ℝ≥0∞ := fun n t =>
    ENNReal.ofReal (Real.exp (-lambda n * t)) *
      Manhattan.annealedContinuousKernel t 0 0
  have hlambdaPos (n : ℕ) : 0 < lambda n := by
    dsimp [lambda]
    positivity
  have hlambdaOne (n : ℕ) : lambda n ≤ 1 := by
    dsimp [lambda]
    exact inv_le_one_of_one_le₀ (by norm_num)
  have hmeas (n : ℕ) : Measurable (f n) := by
    apply Measurable.mul
    · exact ENNReal.continuous_ofReal.measurable.comp (by fun_prop)
    · exact Manhattan.measurable_annealedContinuousKernel 0 0
  have hlambda : Tendsto lambda atTop (𝓝 0) := by
    simpa only [lambda, Nat.cast_add, Nat.cast_one, inv_eq_one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0))
  have hf (t : ℝ) : Tendsto (fun n => f n t) atTop
      (𝓝 (Manhattan.annealedContinuousKernel t 0 0)) := by
    have hexp : Tendsto (fun n => Real.exp (-lambda n * t)) atTop (𝓝 1) := by
      have harg : Tendsto (fun n => -lambda n * t) atTop (𝓝 0) := by
        simpa using hlambda.neg.mul_const t
      exact Real.tendsto_exp_nhds_zero_nhds_one.comp harg
    simpa [f] using ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal hexp)
      (b := Manhattan.annealedContinuousKernel t 0 0) (Or.inl (by norm_num))
  calc
    ∫⁻ t in Ici 0, Manhattan.annealedContinuousKernel t 0 0 =
        ∫⁻ t in Ici 0, liminf (fun n => f n t) atTop := by
          apply setLIntegral_congr_fun measurableSet_Ici
          intro t _
          exact (hf t).liminf_eq.symm
    _ ≤ liminf (fun n => ∫⁻ t in Ici 0, f n t) atTop :=
      lintegral_liminf_le hmeas
    _ ≤ C := liminf_le_of_frequently_le'
      (Frequently.of_forall fun n => hbound (lambda n)
        (hlambdaPos n) (hlambdaOne n))
    _ < ∞ := hC

/-- The exact model identity and a three-region certificate supply Theorem
1.2. This packages the real-to-ENNReal conversion separately from the
model-specific frequency estimates. -/
theorem annealedGreenBound_of_regional_identity
    (green : ℝ → ℝ) (B : Manhattan.Operator.RegionalIntegralBounds green)
    (hidentity : ∀ lambda : ℝ, 0 < lambda →
      (∫⁻ t in Ici 0,
        ENNReal.ofReal (Real.exp (-lambda * t)) *
          Manhattan.annealedContinuousKernel t 0 0) =
        ENNReal.ofReal (green lambda)) :
    Manhattan.AnnealedGreenBound := by
  let C : ℝ := B.smallBound + 2 * B.middleCoefficient + B.outerBound
  apply annealedGreenBound_of_uniform_damped (ENNReal.ofReal C) ENNReal.ofReal_lt_top
  intro lambda hlambda hlambdaOne
  rw [hidentity lambda hlambda]
  exact ENNReal.ofReal_le_ofReal
    (Manhattan.Operator.uniform_green_bound_of_regional_bounds
      B hlambda hlambdaOne)

end Manhattan.Glue
