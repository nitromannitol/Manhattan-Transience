import Manhattan.Paper.TimeDerivative
import Manhattan.Model.Subordination

/-!
# The real kernel of this development is the model's subordinated kernel

`Manhattan.continuousKernel` is `ℝ≥0∞`-valued; `Manhattan.Paper.ck` is the same
object read as a real number.  This file records the identification, the
measurability in the environment, and the `ℝ≥0∞` form of `eq:heat-kernel`.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace Manhattan.Paper

theorem rateTwoPoissonWeight_eq {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    rateTwoPoissonWeight t n = ENNReal.ofReal (poissonWeight t n) := by
  rw [rateTwoPoissonWeight_of_nonneg ht]
  congr 1

theorem continuousKernel_eq_ofReal (ω : Environment) {t : ℝ} (ht : 0 ≤ t) (x y : Site) :
    continuousKernel ω t x y = ENNReal.ofReal (ck ω t x y) := by
  rw [continuousKernel, ck,
    ENNReal.ofReal_tsum_of_nonneg
      (fun n => mul_nonneg (poissonWeight_nonneg ht n) (dk_nonneg ω n x y))
      (summable_ck_terms ω ht x y)]
  refine tsum_congr fun n => ?_
  rw [rateTwoPoissonWeight_eq ht n, ENNReal.ofReal_mul (poissonWeight_nonneg ht n)]
  congr 1
  rw [dk, ENNReal.ofReal_coe_nnreal]

theorem ck_eq_toReal (ω : Environment) {t : ℝ} (ht : 0 ≤ t) (x y : Site) :
    ck ω t x y = (continuousKernel ω t x y).toReal := by
  rw [continuousKernel_eq_ofReal ω ht x y, ENNReal.toReal_ofReal (ck_nonneg ω ht x y)]

/-- Equation `eq:heat-kernel` of `manuscript.tex`, for the model's own kernel. -/
theorem continuousKernel_le (ω : Environment) {t : ℝ} (ht : 0 ≤ t) (x y : Site) :
    continuousKernel ω t x y ≤ ENNReal.ofReal (2 / (t + 2)) := by
  rw [continuousKernel_eq_ofReal ω ht x y]
  exact ENNReal.ofReal_le_ofReal (ck_le_two_div ω ht x y)

/-! ### Measurability in the environment -/

theorem measurable_ck {t : ℝ} (ht : 0 ≤ t) (x y : Site) :
    Measurable fun ω => ck ω t x y := by
  have h : (fun ω : Environment => ck ω t x y)
      = fun ω => (continuousKernel ω t x y).toReal := funext fun ω => ck_eq_toReal ω ht x y
  rw [h]
  exact ((measurable_continuousKernel x y).comp
    (measurable_id.prodMk measurable_const)).ennreal_toReal

theorem measurable_ck_step {t : ℝ} (ht : 0 ≤ t) (x z : Site) (i : Axis) :
    Measurable fun ω => ck ω t (directedNeighbor ω x i) z := by
  classical
  have hset : MeasurableSet {ω : Environment | ω (lineAt x i) = Orientation.positive} := by
    have h := (measurable_pi_apply (lineAt x i) (measurableSet_singleton Orientation.positive) :
      MeasurableSet ((fun f : Environment => f (lineAt x i)) ⁻¹' {Orientation.positive}))
    exact h
  have hfun : (fun ω : Environment => ck ω t (directedNeighbor ω x i) z)
      = fun ω => if ω (lineAt x i) = Orientation.positive
          then ck ω t (x + (1 : ℤ) • basisStep i) z
          else ck ω t (x + (-1 : ℤ) • basisStep i) z := by
    funext ω
    by_cases h : ω (lineAt x i) = Orientation.positive
    · simp [h, directedNeighbor]
    · have h' : ω (lineAt x i) = Orientation.negative := by
        cases hh : ω (lineAt x i) with
        | negative => rfl
        | positive => exact absurd hh h
      simp [h', directedNeighbor, Orientation.sign]
  rw [hfun]
  exact Measurable.ite hset (measurable_ck ht _ z) (measurable_ck ht _ z)

theorem measurable_dck {t : ℝ} (ht : 0 ≤ t) (x z : Site) :
    Measurable fun ω => dck ω t x z := by
  have h : (fun ω : Environment => dck ω t x z)
      = fun ω => ck ω t (directedNeighbor ω x Axis.horizontal) z
        + ck ω t (directedNeighbor ω x Axis.vertical) z - 2 * ck ω t x z := rfl
  rw [h]
  exact ((measurable_ck_step ht x z Axis.horizontal).add
    (measurable_ck_step ht x z Axis.vertical)).sub ((measurable_ck ht x z).const_mul 2)

theorem integrable_ck {t : ℝ} (ht : 0 ≤ t) (x y : Site) :
    Integrable (fun ω => ck ω t x y) environmentLaw := by
  refine Integrable.mono' (integrable_const (1:ℝ))
    (measurable_ck ht x y).aestronglyMeasurable ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (ck_nonneg ω ht x y)]
  exact ck_le_one ω ht x y

/-- The annealed return probability `f(t) = p̄_t(0,0)`, as a real number. -/
noncomputable def annealedReal (t : ℝ) : ℝ := ∫ ω, ck ω t 0 0 ∂environmentLaw

theorem annealedContinuousKernel_eq {t : ℝ} (ht : 0 ≤ t) :
    annealedContinuousKernel t 0 0 = ENNReal.ofReal (annealedReal t) := by
  rw [annealedReal,
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal (integrable_ck ht 0 0)
      (Filter.Eventually.of_forall fun ω => ck_nonneg ω ht 0 0), annealedContinuousKernel]
  exact lintegral_congr fun ω => continuousKernel_eq_ofReal ω ht 0 0

end Manhattan.Paper
