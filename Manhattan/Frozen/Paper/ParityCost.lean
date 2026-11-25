import Manhattan.Paper.EffectiveEnergy

/-! Equations `eq:scalar-energy` and `eq:parity-energy` of the arXiv version, integrated
(`paper/arxiv/main.tex:868-901`): at the minimizer `V = w/(B + σ)`, for bounded
measurable `w` and every majorant constant `κ > 0`, the degree-three density `σ V²` and
the mixed residual `(w - σV)²/B` integrate to `∫ w² ∫ dm(β)/(B + σ)`. -/

open scoped lp
open MeasureTheory Set UnitAddTorus
open Manhattan Manhattan.Glue Manhattan.V4.Frequency Manhattan.Paper
open LatticeProb.Analysis

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Paper.parityCost_eq {kappa delta Kw : ℝ} {q : Estimates.Parameters}
    (hlam : 0 < q.lambda) (hkappa : 0 < kappa) (hdelta : 0 < delta)
    {w : ℝ → ℝ} (hmw : Measurable w) (hbw : ∀ r, |w r| ≤ Kw) :
    (Estimates.torusIntegral fun beta => Estimates.torusIntegral fun r =>
        V4.paritySigma kappa delta r beta
          * V4.parityV q kappa delta (fun r' _ => w r') r beta ^ 2)
      + (Estimates.torusIntegral fun r => Estimates.torusIntegral fun beta =>
        (w r - V4.paritySigma kappa delta r beta
            * V4.parityV q kappa delta (fun r' _ => w r') r beta) ^ 2
          / Estimates.correctionB q r beta)
      = Estimates.torusIntegral (fun r => w r ^ 2 * V4.parityFibreJ q kappa delta r)
-- FROZEN-STATEMENT-END
:= Manhattan.Paper.parityCost_eq hlam hkappa hdelta hmw hbw
