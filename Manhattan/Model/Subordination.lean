import Manhattan.Model.Kernel
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Distributions.Poisson

/-!
# Rate-two Poisson subordination

Following, the continuous-time kernel is *defined* by Poisson
subordination of the discrete jump chain.  The generator calculation is the
elementary lemma in `Manhattan.Model.Kernel`.

Paper: `manuscript.tex:200-226` and `manuscript.tex:688-693`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

namespace Manhattan

/-- The probability `P(N_t=n)` for a rate-two Poisson process.  It is set to
zero at negative times so that ordinary Lebesgue integration on `ℝ` can be
used without a separate subtype carrier. -/
noncomputable def rateTwoPoissonWeight (t : ℝ) (n : ℕ) : ℝ≥0∞ :=
  if ht : 0 ≤ t then
    ENNReal.ofReal (poissonPMFReal ⟨2 * t, mul_nonneg (by norm_num) ht⟩ n)
  else 0

theorem rateTwoPoissonWeight_of_nonneg {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    rateTwoPoissonWeight t n =
      ENNReal.ofReal (poissonPMFReal ⟨2 * t, mul_nonneg (by norm_num) ht⟩ n) := by
  simp [rateTwoPoissonWeight, ht]

theorem rateTwoPoissonWeight_of_neg {t : ℝ} (ht : t < 0) (n : ℕ) :
    rateTwoPoissonWeight t n = 0 := by
  simp [rateTwoPoissonWeight, not_le.mpr ht]

/-- The time profile of a Poisson coefficient is one half of the Erlang
density with shape `n+1` and rate `2`. -/
theorem rateTwoPoissonWeight_eq_half_gamma (t : ℝ) (n : ℕ) :
    rateTwoPoissonWeight t n =
      (2 : ℝ≥0∞)⁻¹ * gammaPDF (n + 1 : ℝ) 2 t := by
  by_cases ht : 0 ≤ t
  · rw [rateTwoPoissonWeight_of_nonneg ht, gammaPDF_of_nonneg ht]
    rw [poissonPMFReal, Real.Gamma_nat_eq_factorial]
    rw [show (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) by norm_num]
    simp only [NNReal.coe_mk, Nat.cast_add, Nat.cast_one, add_sub_cancel_right,
      Real.rpow_natCast]
    rw [show (2 : ℝ≥0∞)⁻¹ = ENNReal.ofReal ((2 : ℝ)⁻¹) by
      symm
      rw [ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]]
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (2 : ℝ)⁻¹)]
    congr 1
    rw [mul_pow, Real.rpow_add_one (by norm_num), Real.rpow_natCast]
    ring
  · have ht' := lt_of_not_ge ht
    rw [rateTwoPoissonWeight_of_neg ht', gammaPDF_of_neg ht']
    simp

theorem measurable_rateTwoPoissonWeight (n : ℕ) :
    Measurable fun t => rateTwoPoissonWeight t n := by
  simp_rw [rateTwoPoissonWeight_eq_half_gamma]
  exact (measurable_gammaPDFReal (n + 1 : ℝ) 2).ennreal_ofReal.const_mul _

/-- Poisson weights at a fixed nonnegative time sum to one. -/
theorem rateTwoPoissonWeight_tsum {t : ℝ} (ht : 0 ≤ t) :
    ∑' n : ℕ, rateTwoPoissonWeight t n = 1 := by
  simp_rw [rateTwoPoissonWeight_of_nonneg ht]
  exact (poissonPMF ⟨2 * t, mul_nonneg (by norm_num) ht⟩).property.tsum_eq

/-- The continuous-time quenched kernel, by rate-two Poisson subordination. -/
noncomputable def continuousKernel (ω : Environment) (t : ℝ) (z z' : Site) : ℝ≥0∞ :=
  ∑' n : ℕ, rateTwoPoissonWeight t n * nStepKernel ω n z z'

/-- The annealed continuous-time kernel. -/
noncomputable def annealedContinuousKernel (t : ℝ) (z z' : Site) : ℝ≥0∞ :=
  ∫⁻ ω, continuousKernel ω t z z' ∂environmentLaw

/-- Each Poisson coefficient has total time mass `1/2`. -/
theorem lintegral_rateTwoPoissonWeight (n : ℕ) :
    ∫⁻ t in Ici 0, rateTwoPoissonWeight t n = (2 : ℝ≥0∞)⁻¹ := by
  simp_rw [rateTwoPoissonWeight_eq_half_gamma]
  have hgamma : Measurable (gammaPDF (n + 1 : ℝ) 2) :=
    (measurable_gammaPDFReal (n + 1 : ℝ) 2).ennreal_ofReal
  rw [lintegral_const_mul _ hgamma]
  have hneg : ∫⁻ t in (Ici (0 : ℝ))ᶜ, gammaPDF (n + 1 : ℝ) 2 t = 0 := by
    calc
      _ = ∫⁻ _t in (Ici (0 : ℝ))ᶜ, 0 := by
        apply setLIntegral_congr_fun measurableSet_Ici.compl
        intro t ht
        exact gammaPDF_of_neg (by simpa only [Set.mem_compl_iff, mem_Ici, not_le] using ht)
      _ = 0 := lintegral_zero
  have hpos : ∫⁻ t in Ici 0, gammaPDF (n + 1 : ℝ) 2 t = 1 := by
    calc
      _ = (∫⁻ t in Ici 0, gammaPDF (n + 1 : ℝ) 2 t) + 0 := by simp
      _ = (∫⁻ t in Ici 0, gammaPDF (n + 1 : ℝ) 2 t) +
          ∫⁻ t in (Ici (0 : ℝ))ᶜ, gammaPDF (n + 1 : ℝ) 2 t := by rw [hneg]
      _ = ∫⁻ t, gammaPDF (n + 1 : ℝ) 2 t :=
        lintegral_add_compl _ measurableSet_Ici
      _ = 1 := lintegral_gammaPDF_eq_one (by positivity) (by norm_num)
  rw [hpos, mul_one]

/-- The time integral of the subordinated return kernel is half the discrete
Green series, as in `manuscript.tex:690-693`. -/
theorem lintegral_continuousKernel_eq_half_tsum
    (ω : Environment) (z z' : Site) :
    ∫⁻ t in Ici 0, continuousKernel ω t z z' =
      (2 : ℝ≥0∞)⁻¹ * ∑' n : ℕ, (nStepKernel ω n z z' : ℝ≥0∞) := by
  simp only [continuousKernel]
  rw [lintegral_tsum]
  · calc
      _ = ∑' n : ℕ, (2 : ℝ≥0∞)⁻¹ * nStepKernel ω n z z' := by
        apply tsum_congr
        intro n
        rw [lintegral_mul_const _ (measurable_rateTwoPoissonWeight n),
          lintegral_rateTwoPoissonWeight]
      _ = _ := ENNReal.tsum_mul_left
  · intro n
    exact (measurable_rateTwoPoissonWeight n).aemeasurable.mul_const
      (nStepKernel ω n z z')

/-- Joint measurability of the subordinated kernel in environment and time. -/
theorem measurable_continuousKernel (z z' : Site) :
    Measurable fun q : Environment × ℝ => continuousKernel q.1 q.2 z z' := by
  apply Measurable.ennreal_tsum
  intro n
  exact ((measurable_rateTwoPoissonWeight n).comp measurable_snd).mul
    ((measurable_nStepKernel n z z').coe_nnreal_ennreal.comp measurable_fst)

theorem measurable_annealedContinuousKernel (z z' : Site) :
    Measurable fun t => annealedContinuousKernel t z z' := by
  have h : Measurable fun q : ℝ × Environment => continuousKernel q.2 q.1 z z' :=
    (measurable_continuousKernel z z').comp (measurable_snd.prodMk measurable_fst)
  exact Measurable.lintegral_prod_right h

/-- The full assertion of Theorem 1.2, placed with the subordinated kernel so
the final Glue provider can be imported by `Model.Theorem12` without a cycle. -/
def AnnealedGreenBound : Prop :=
  ∃ C : ℝ≥0∞, C < ∞ ∧
    (∀ lambda : ℝ, 0 < lambda → lambda ≤ 1 →
      ∫⁻ t in Ici 0,
        ENNReal.ofReal (Real.exp (-lambda * t)) * annealedContinuousKernel t 0 0 ≤ C) ∧
    ∫⁻ t in Ici 0, annealedContinuousKernel t 0 0 < ∞

end Manhattan
