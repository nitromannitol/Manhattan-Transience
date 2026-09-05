import Manhattan.Model.Subordination
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Theorem 1.1 from Theorem 1.2

Paper: `manuscript.tex:192-198` and `manuscript.tex:685-697`.
-/

open MeasureTheory Set Filter
open scoped ENNReal

namespace Manhattan

/-- The quenched discrete Green series. -/
noncomputable def discreteGreen (ω : Environment) (x : Site) : ℝ≥0∞ :=
  ∑' n : ℕ, (nStepKernel ω n x x : ℝ≥0∞)

theorem measurable_discreteGreen (x : Site) : Measurable fun ω => discreteGreen ω x := by
  exact Measurable.ennreal_tsum fun n =>
    (measurable_nStepKernel n x x).coe_nnreal_ennreal

theorem discreteGreen_translate (x : Site) (ω : Environment) :
    discreteGreen ω x = discreteGreen (translateEnvironment x ω) 0 := by
  apply tsum_congr
  intro n
  exact_mod_cast nStepKernel_return_translate x ω n

private theorem discreteGreen_origin_ae_lt_top (h : AnnealedGreenBound) :
    ∀ᵐ ω ∂environmentLaw, discreteGreen ω 0 < ∞ := by
  rcases h with ⟨C, hC, hlaplace, hfull⟩
  have hjoint : AEMeasurable
      (Function.uncurry fun ω t => continuousKernel ω t 0 0)
      (environmentLaw.prod (volume.restrict (Ici 0))) :=
    (measurable_continuousKernel 0 0).aemeasurable
  have hswap :
      (∫⁻ ω, ∫⁻ t in Ici 0, continuousKernel ω t 0 0 ∂volume ∂environmentLaw) =
        ∫⁻ t in Ici 0, annealedContinuousKernel t 0 0 := by
    change (∫⁻ ω, ∫⁻ t in Ici 0, continuousKernel ω t 0 0 ∂volume ∂environmentLaw) =
      ∫⁻ t in Ici 0, ∫⁻ ω, continuousKernel ω t 0 0 ∂environmentLaw
    exact lintegral_lintegral_swap hjoint
  have hiterated :
      (∫⁻ ω, ∫⁻ t in Ici 0, continuousKernel ω t 0 0 ∂volume ∂environmentLaw) < ∞ := by
    rwa [hswap]
  have hinnerMeas : Measurable fun ω =>
      ∫⁻ t in Ici 0, continuousKernel ω t 0 0 :=
    Measurable.lintegral_prod_right (measurable_continuousKernel 0 0)
  filter_upwards [ae_lt_top hinnerMeas hiterated.ne] with ω hω
  rw [lintegral_continuousKernel_eq_half_tsum] at hω
  change (2 : ℝ≥0∞)⁻¹ * discreteGreen ω 0 < ∞ at hω
  rcases ENNReal.mul_lt_top_iff.mp hω with hfinite | hzero | hgreenZero
  · exact hfinite.2
  · norm_num at hzero
  · simp [hgreenZero]

/-- Theorem 1.1, with the annealed assertion of Theorem 1.2 as its only
hypothesis: almost surely every site has a finite quenched Green series. -/
theorem theorem_1_1 (h : AnnealedGreenBound) :
    ∀ᵐ ω ∂environmentLaw, ∀ x : Site, discreteGreen ω x < ∞
  := by
  have hzero := discreteGreen_origin_ae_lt_top h
  rw [ae_all_iff]
  intro x
  have hx : ∀ᵐ ω ∂environmentLaw,
      discreteGreen (translateEnvironment x ω) 0 < ∞ :=
    (measurePreserving_translateEnvironment x).quasiMeasurePreserving.tendsto_ae hzero
  exact hx.mono fun ω hω => by rwa [discreteGreen_translate]

end Manhattan
