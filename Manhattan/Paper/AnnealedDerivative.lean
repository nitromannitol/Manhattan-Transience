/-
The annealed form of `eq:time-derivative`.

`prop:time` states its second bound for `f(t) = p̄_t(0,0)`, the annealed return
probability, so the quenched bound has to be carried through the environment
average.  The quenched derivative is bounded uniformly in the environment, and
the environment law is a probability measure, so differentiation under the
integral applies and the same bound survives averaging.
-/
import Manhattan.Paper.TimeDerivative
import Manhattan.Paper.ModelLink
import Mathlib.Analysis.Calculus.ParametricIntegral

namespace Manhattan.Paper

open MeasureTheory

/-- The quenched derivative is bounded uniformly in the environment and locally
uniformly in time. -/
theorem abs_dck_le_const {t s : ℝ} (ht : 0 < t) (hs : t / 2 < s) (ω : Environment) :
    |dck ω s 0 0| ≤ 2 / Real.sqrt (t / 2) := by
  have hs0 : 0 < s := lt_trans (by linarith) hs
  refine (abs_dck_le_paper ω hs0 0 0).trans ?_
  have h1 : Real.sqrt (t / 2) ≤ Real.sqrt s := Real.sqrt_le_sqrt hs.le
  have h2 : (0:ℝ) < Real.sqrt (t / 2) := Real.sqrt_pos.mpr (by linarith)
  have h3 : (0:ℝ) < Real.sqrt s := Real.sqrt_pos.mpr hs0
  rw [div_le_div_iff₀ (by positivity) h2]
  nlinarith [h1, h2, h3, hs0.le]

/-- **The annealed return probability is differentiable**, with derivative the
average of the quenched derivative. -/
theorem hasDerivAt_annealedReal {t : ℝ} (ht : 0 < t) :
    HasDerivAt annealedReal (∫ ω, dck ω t 0 0 ∂environmentLaw) t := by
  have hε : (0:ℝ) < t / 2 := by linarith
  have hball : ∀ s ∈ Metric.ball t (t / 2), t / 2 < s := by
    intro s hs
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hs
    linarith [hs.1]
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := fun s ω => ck ω s 0 0)
    (F' := fun s ω => dck ω s 0 0) (bound := fun _ => 2 / Real.sqrt (t / 2)) hε
    ?_ (integrable_ck ht.le 0 0) ((measurable_dck ht.le 0 0).aestronglyMeasurable)
    ?_ (integrable_const _) ?_).2
  · filter_upwards [Metric.ball_mem_nhds t hε] with s hs
    exact (measurable_ck (lt_trans (by linarith) (hball s hs)).le 0 0).aestronglyMeasurable
  · filter_upwards with ω s hs
    rw [Real.norm_eq_abs]
    exact abs_dck_le_const ht (hball s hs) ω
  · filter_upwards with ω s hs
    exact hasDerivAt_ck ω (lt_trans (by linarith) (hball s hs)) 0 0

/-- **Equation `eq:time-derivative` of `manuscript.tex`, annealed form.** -/
theorem abs_deriv_annealedReal_le {t : ℝ} (ht : 0 < t) :
    |deriv annealedReal t| ≤ 2 / (Real.sqrt t * (1 + t / 4)) := by
  rw [(hasDerivAt_annealedReal ht).deriv]
  refine (abs_integral_le_integral_abs).trans ?_
  have hbound : ∀ ω : Environment, |dck ω t 0 0| ≤ 2 / (Real.sqrt t * (1 + t / 4)) :=
    fun ω => abs_dck_le_paper ω ht 0 0
  have hintd : Integrable (fun ω : Environment => dck ω t 0 0) environmentLaw := by
    refine Integrable.mono' (integrable_const (2 / (Real.sqrt t * (1 + t / 4))))
      ((measurable_dck ht.le 0 0).aestronglyMeasurable) ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs]
    exact hbound ω
  have hint : Integrable (fun ω : Environment => |dck ω t 0 0|) environmentLaw := hintd.abs
  calc ∫ ω, |dck ω t 0 0| ∂environmentLaw
      ≤ ∫ _ω : Environment, 2 / (Real.sqrt t * (1 + t / 4)) ∂environmentLaw :=
        integral_mono hint (integrable_const _) hbound
    _ = 2 / (Real.sqrt t * (1 + t / 4)) := by
        rw [integral_const]; simp

/-- The `8 t^{-3/2}` form, annealed. -/
theorem abs_deriv_annealedReal_le_pow {t : ℝ} (ht : 0 < t) :
    |deriv annealedReal t| ≤ 8 / (t * Real.sqrt t) := by
  refine (abs_deriv_annealedReal_le ht).trans ?_
  have hsqrtpos : (0:ℝ) < Real.sqrt t := Real.sqrt_pos.2 ht
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hsqrtpos, ht]

end Manhattan.Paper
