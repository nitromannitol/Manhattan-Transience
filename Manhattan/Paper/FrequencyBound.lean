import Manhattan.Paper.EffectiveEnergy
import Manhattan.Paper.Constant.GreenConstant

/-!
# `prop:frequency` with the constant `2048`

`prop:frequency` (`paper/arxiv/main.tex:1070-1092`): for every `λ ∈ (0,1]` and
`p ∈ 𝕋²`, with `a(p) = max(|p₁|, |p₂|)`,

    r_λ(p) ≤ 2048 / (λ + a(p)² [1 + log₊(1/(√λ + a(p)))]^{3/2}).

`Manhattan.V4.Frequency.V4FrequencyBound C` is this inequality with the
constant `C`.  On `δ = √λ + a(p) ≤ 1/256` the bound `eq:optimized` with the
constant `16` (`Manhattan.Paper.move2Supply_sixteen`) and the lower bound on
`Z_δ` give the constant `10π²·16 < 1580`
(`Manhattan.Paper.Constant.v4FrequencyBound_tight`); on `δ > 1/256` the zero
function gives the constant `Manhattan.V4.Frequency.outerRegionConstant (1/4) ≤ 83`.
-/

open Manhattan Manhattan.V4.Frequency

namespace Manhattan.Paper

/-- The frequency bound is monotone in its constant. -/
theorem v4FrequencyBound_mono {C C' : ℝ} (hC : C ≤ C') (h : V4FrequencyBound C) :
    V4FrequencyBound C' := by
  intro lambda hlambda hlambda1 p hp0 hp1
  exact (h lambda hlambda hlambda1 p hp0 hp1).trans
    (mul_le_mul_of_nonneg_right hC (v4Majorant_pos hlambda p).le)

/-- **`prop:frequency`** (`paper/arxiv/main.tex:1070-1092`), with the constant
`2048` of the paper. -/
theorem frequencyBound_2048 : V4FrequencyBound 2048 := by
  have h := Constant.v4FrequencyBound_tight (r0 := 1 / 4) (by norm_num) le_rfl
    (by norm_num : (0:ℝ) < 16) (move2Supply_sixteen (by norm_num) le_rfl)
  refine v4FrequencyBound_mono ?_ h
  refine max_le (max_le (by norm_num) ?_) (Constant.outerRegionConstant_quarter_le.trans
    (by norm_num))
  nlinarith [Constant.pi_sq_le]

end Manhattan.Paper
