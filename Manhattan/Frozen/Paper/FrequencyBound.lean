import Manhattan.Paper.FrequencyBound

/-! Proposition 6.1 of the arXiv version (`prop:frequency`, `paper/arxiv/main.tex:1070-1092`)
with the printed constant `2048`: for every `λ ∈ (0,1]` and `p ∈ 𝕋²`,
`r_λ(p) ≤ 2048/(λ + a(p)² [1 + log₊(1/(√λ + a(p)))]^{3/2})`.  The proof reaches the
constant `max(10π² · 16, 83) < 1580`. -/

open Manhattan Manhattan.V4.Frequency Manhattan.Paper

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Paper.frequencyBound_2048 : V4FrequencyBound 2048
-- FROZEN-STATEMENT-END
:= Manhattan.Paper.frequencyBound_2048
