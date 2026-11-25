import Manhattan.Paper.LemmaFour

/-! Lemma 5.2 (`lem:four`, `manuscript.tex:1200-1207`): there is `κ > 0` (the proof gives
`κ = 97`) such that every `k ∈ ℋ₃` satisfies `⟨k, H₃ k⟩ + ‖D₃ k‖²_{H⁻¹} ≤ ⟨k, M k⟩` for the
multiplier `M` of `eq:M`, with integrable integrands. -/

open MeasureTheory UnitAddTorus
open Manhattan Manhattan.Glue Manhattan.Paper

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Paper.lemma_four :
    ∃ kappa : ℝ, 0 < kappa ∧
      ∀ (q : Estimates.Parameters) (hlambda : 0 < q.lambda) (p : Fin 2 → ℝ),
      ∀ k ∈ Manhattan.walshDegree 3, ∃ g : DegreeCoefficient 3,
        homogeneousWalshSynthesis 3 g = k ∧
        (∀ σ : Fin 3 → Axis, Integrable (fun t =>
            Estimates.multiplier kappa q (totalFrequency 3 p σ t) *
              ‖((lineIndexFourier 3 g) σ : UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2)
            (LineTorusMeasure 3)) ∧
        sectorHThreeForm q.lambda p k + sectorDFourForm hlambda p k ≤
          ∑' σ : Fin 3 → Axis, ∫ t, Estimates.multiplier kappa q (totalFrequency 3 p σ t) *
            ‖((lineIndexFourier 3 g) σ : UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2
            ∂(LineTorusMeasure 3)
-- FROZEN-STATEMENT-END
:= Manhattan.Paper.lemma_four
