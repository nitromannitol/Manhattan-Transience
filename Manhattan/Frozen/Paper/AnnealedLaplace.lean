import Manhattan.Paper.AnnealedConstant

/-! Theorem 1.2 of the arXiv version (`thm:annealed`, `paper/arxiv/main.tex:180-188`, proof
at `:1094-1121`) with the printed constant `2048`: for every `λ ∈ (0,1]`,
`∫₀^∞ e^{-λt} p̄_t(0,0) dt ≤ 2048`.  The proof reaches about `1578`. -/

open MeasureTheory Set Filter Topology
open scoped ENNReal
open Manhattan Manhattan.V4.Frequency Manhattan.Estimates Manhattan.Paper

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Paper.annealed_laplace_le_2048 {lambda : ℝ} (hlambda : 0 < lambda) (hlambda1 : lambda ≤ 1) :
    (∫⁻ t in Ici (0:ℝ), ENNReal.ofReal (Real.exp (-lambda * t)) *
        Manhattan.annealedContinuousKernel t 0 0) ≤ ENNReal.ofReal 2048
-- FROZEN-STATEMENT-END
:= Manhattan.Paper.annealed_laplace_le_2048 hlambda hlambda1
