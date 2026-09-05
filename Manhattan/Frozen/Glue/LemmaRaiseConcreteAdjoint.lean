import Manhattan.Glue.ConcreteLowering

/-! Frozen Lemma 5.1 anchor, adjoint side: the concrete Walsh coefficients of
`D* x` in the Finset isometry (`lem:raise`, `manuscript.tex:1179-1191`). -/

open MeasureTheory
open scoped BigOperators
open Manhattan Manhattan.Glue

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Glue.lemma_raise_concrete_adjoint (p : Fin 2 → ℝ) (x : WalshL2)
    (S : Finset LineIndex) :
    loweringCoefficient p x S =
      ∑ i : Fin 2,
        (((2 : ℂ)⁻¹ * Complex.exp (-Complex.I * p i)) *
            walshCoefficientAt x (toggleOriginWalshIndex i
              (translateWalshIndex (Operator.axisVector i) S)) -
          ((2 : ℂ)⁻¹ * Complex.exp (Complex.I * p i)) *
            walshCoefficientAt x (toggleOriginWalshIndex i
              (translateWalshIndex (-Operator.axisVector i) S)))
-- FROZEN-STATEMENT-END
:= Manhattan.Glue.loweringCoefficient_eq p x S
