import Manhattan.Estimates.TargetStatements

/-!
# Audited obstructions in the stage candidate surface

These theorems make two statement defects kernel-checkable. They do not
alter the candidate statements.
-/

open Set

namespace Manhattan.Estimates

noncomputable section

/-- The mixed residual in the candidate Lemma 4.1 vanishes at `p₁ = 0`. -/
theorem mixedResidualHMinusSq_zero_frequency (q : Parameters) :
    mixedResidualHMinusSq q 0 = 0 := by
  simp [mixedResidualHMinusSq, mixedResidual, degreeOneCoefficient, torusIntegral]

/-- Whenever the logarithmic regime is nonempty at zero frequency, the
candidate `LemmaFourTwoClaim` is contradictory: its positive lower bound is
applied to the identically zero signed residual.

The missing source-side hypothesis is `0 < |p₁|`; the only use of Lemma 4.1
in the manuscript later imposes it at `manuscript.tex:1137`.
-/
theorem not_lemmaFourTwoClaim_of_zero_frequency
    {K rho lambda : ℝ} (hK : 20 ≤ K) (hrhoPos : 0 < rho)
    (hrho : rho ≤ Real.pi / 20) (hlambda : 0 < lambda) (hlambdaOne : lambda ≤ 1)
    (hlog : (Parameters.logThreshold ⟨lambda, K, rho⟩) <
      Parameters.scaleLog ⟨lambda, K, rho⟩ 0) :
    ¬ LemmaFourTwoClaim K rho := by
  intro hclaim
  obtain ⟨c, C, hc, _hC, h⟩ := hclaim hK hrhoPos hrho
  have hzeroTorus : (0 : ℝ) ∈ torus := by
    exact ⟨neg_lt_zero.mpr Real.pi_pos, Real.pi_pos.le⟩
  have hlog' : (Parameters.logThreshold ⟨lambda, K, rho⟩) <
      Parameters.scaleLog ⟨lambda, K, rho⟩ |0| := by simpa only [abs_zero] using hlog
  have hz := h lambda hlambda hlambdaOne 0 0 hzeroTorus hzeroTorus
    (by simp) hlog'
  have hlower := hz.2.2.2.2.1
  rw [mixedResidualHMinusSq_zero_frequency] at hlower
  simp only [abs_zero] at hlower
  have hthresholdPos : 0 < Parameters.logThreshold ⟨lambda, K, rho⟩ := by
    dsimp [Parameters.logThreshold]
    have hlogK : 0 < Real.log K := Real.log_pos (by linarith)
    linarith
  have hscalePos : 0 < Parameters.scaleLog ⟨lambda, K, rho⟩ 0 :=
    hthresholdPos.trans hlog
  nlinarith

/-- The unrestricted Section 5 interface is false for constant forms. -/
theorem not_lemmaSixTwoInterface_unit :
    ¬ LemmaSixTwoInterface (E := Unit) (fun _ => 1) (fun _ => 1) (fun _ => 0) := by
  intro h
  have := h ()
  norm_num at this

/-- The certificate candidate stores four propositions rather than proofs of
them, so it is inhabited even when every stored proposition is false. -/
theorem lemmaSixFourCertificate_vacuously_inhabited : Nonempty LemmaSixFourCertificate :=
  ⟨⟨False, False, False, False⟩⟩

end

end Manhattan.Estimates
