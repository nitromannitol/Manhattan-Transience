import Manhattan.Paper.AnnealedConstant

/-! Theorem 1.2 of the arXiv version (`thm:annealed`, `paper/arxiv/main.tex:180-188`, proof
at `:1097-1121`) with the printed constant `2048`: for every `λ ∈ (0,1]`,
`∫₀^∞ e^{-λt} p̄_t(0,0) dt ≤ 2048`.  The proof uses Proposition 6.1 with `2048` and
reaches `1/π² + 2^{7/2}·2048/(π²√(1 + log 4)) + log(4π) ≈ 1522.4`, the computation of
`paper/arxiv/main.tex:1105-1113`. -/

open MeasureTheory Set Filter Topology
open scoped ENNReal
open Manhattan Manhattan.V4.Frequency Manhattan.Estimates Manhattan.Paper

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Paper.annealed_laplace_le_2048 {lambda : ℝ} (hlambda : 0 < lambda) (hlambda1 : lambda ≤ 1) :
    (∫⁻ t in Ici (0:ℝ), ENNReal.ofReal (Real.exp (-lambda * t)) *
        Manhattan.annealedContinuousKernel t 0 0) ≤ ENNReal.ofReal 2048
-- FROZEN-STATEMENT-END
:= Manhattan.Paper.annealed_laplace_le_2048 hlambda hlambda1
