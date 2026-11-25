import Manhattan.Paper.EffectiveEnergy

/-! Equation `eq:uncancelled` of the arXiv version (`paper/arxiv/main.tex:966-973`), for
`f` of degree one carrying only row signs and `k` of type `112` with `(D₂* k)₁₁ = 0`:
the objective of `lem:variational-bound` equals the uncancelled degree-zero term plus
the summands of `eq:E`, the degree-two summand split into its two-row and mixed
sectors.  Hypothesis: the degree-zero coefficient `⟨1, 1 - A_p(f + k)⟩` is a real number
`c` (`hc`); the degree-zero term is `c²/(λ + θ(p))`. -/

open scoped lp
open MeasureTheory Set UnitAddTorus
open Manhattan Manhattan.Glue Manhattan.V4.Frequency Manhattan.Paper
open LatticeProb.Analysis

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Paper.objective_eq_sectors {lambda : ℝ} (hlambda : 0 < lambda)
    (p : Fin 2 → ℝ) {cc : ℝ} (c : Manhattan.RowLineCoefficient)
    (kc : ℓ²(Manhattan.Type112Index, ℂ))
    (hk : Manhattan.type112DStarTwoRow p kc = 0)
    (hc : inner ℂ (Manhattan.walshL2 ∅)
        (unnormalizedResidual p 1
          (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal c)
          (Manhattan.type112WalshSynthesis kc)) = ((cc : ℝ) : ℂ)) :
    (concreteFiberEnvironment.dissipativeSkewPair p).hEnergy lambda
        (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal c
          + Manhattan.type112WalshSynthesis kc)
      + (concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hlambda
          (Manhattan.walshL2 ∅ - concreteFiberA p
            (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal c
              + Manhattan.type112WalshSynthesis kc))
      = cc ^ 2 / (lambda + Operator.theta p)
        + (concreteFiberEnvironment.dissipativeSkewPair p).hEnergy lambda
            (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal c)
        + (concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hlambda
            (Manhattan.type11WalshSynthesis (Manhattan.type11WalshAnalysis
              (walshRaise p (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal c))))
        + (sectorHThreeForm lambda p (Manhattan.type112WalshSynthesis kc)
            + sectorDFourForm hlambda p (Manhattan.type112WalshSynthesis kc))
        + (concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hlambda
            (Manhattan.type12WalshSynthesis
              (Manhattan.type12WalshAnalysis (walshRaise p
                  (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal c))
                - Manhattan.type112DStarMixed p kc))
-- FROZEN-STATEMENT-END
:= Manhattan.Paper.objective_eq_sectors hlambda p c kc hk hc
