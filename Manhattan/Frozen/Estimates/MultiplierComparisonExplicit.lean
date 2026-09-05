import Manhattan.Estimates.RankOne

/-! Frozen proved explicit estimate. -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Estimates.multiplier_comparison_explicit : ∀ {K rho lambda beta alpha : ℝ},
  20 ≤ K →
    rho ≤ Real.pi / 20 →
      0 < lambda →
        lambda ≤ 1 →
          |alpha| ≤ rho →
            4 * K * (√lambda + |beta|) ≤ |alpha| →
              have q := { lambda := lambda, K := K, rho := rho };
              80 / Real.pi * |alpha| ≤
                  Manhattan.Estimates.multiplier 40 q (Manhattan.Estimates.mixedTotalFrequency beta alpha) ∧
                Manhattan.Estimates.multiplier 40 q (Manhattan.Estimates.mixedTotalFrequency beta alpha) ≤ 200 * |alpha|
-- FROZEN-STATEMENT-END
:= @Manhattan.Estimates.multiplier_comparison_explicit
