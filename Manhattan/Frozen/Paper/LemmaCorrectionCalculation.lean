import Manhattan.Paper.LemmaCorrection

/-! Lemma 5.4 (`lem:correction-calculation`, `manuscript.tex:1305-1420`) at the operator
level, for the degree-three part `k_p = sgn(sin p₁) Π₃ k̃` of the concrete competitor and
`w = sgn(sin p₁) 1_I`, the mixed component of `D₁ f_p`: `(D₂* k_p)₁₁ = 0`, and `eq:reduce`
holds with the constant `26 + 12/(K³ρ)` and the multiplier `M` of `eq:M` at `κ = 40`.
Hypotheses: admissible parameters, `|p₂| ≤ |p₁|` and `K δ < r₀` (those of `prop:key`),
`b_p ≠ 0` (which excludes `p₁ = 0`), and the integrability certificate
`LemmaFourTwoIntegralCertificate`, which
`Manhattan.Estimates.lemmaFourTwoIntegralCertificate_proved` supplies when `p₁ ≠ 0`. -/

open scoped lp
open MeasureTheory UnitAddTorus
open Manhattan Manhattan.Glue Manhattan.Paper
open Manhattan.Estimates

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Paper.lemma_correction_calculation {q : Parameters} (hq : q.Admissible)
    {p : Fin 2 → ℝ} (hp₂ : |p 1| ≤ |p 0|) (hsupp : q.K * q.delta |p 0| < q.r0)
    (hcert : LemmaFourTwoIntegralCertificate q (p 0) (p 1))
    (hnormalization : degreeOneNormalization q (p 0) ≠ 0) :
    type112DStarTwoRow p
        (correctedLowDegreeData hq.1 p hcert hnormalization).mixedCoefficient = 0 ∧
      (concreteFiberEnvironment.dissipativeSkewPair p).hEnergy q.lambda
          (correctedMixedVector (correctedLowDegreeData hq.1 p hcert hnormalization)) +
        (concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hq.1
          (walshSectorComponent (fun S => S.card = 4)
            (concreteFiberA p
              (correctedMixedVector (correctedLowDegreeData hq.1 p hcert hnormalization)))) +
        (concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hq.1
          (type12WalshSynthesis (type12WalshAnalysis (walshRaise p
              (correctedRowVector (correctedLowDegreeData hq.1 p hcert hnormalization)))) -
            type112DStar p
              (correctedLowDegreeData hq.1 p hcert hnormalization).mixedCoefficient) ≤
        reduceConstant q * correctionReducedIntegral q |p 0|
-- FROZEN-STATEMENT-END
:= Manhattan.Paper.lemma_correction_calculation hq hp₂ hsupp hcert hnormalization
