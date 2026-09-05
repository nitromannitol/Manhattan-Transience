import Manhattan.Glue.ConcreteRaising

/-! Frozen Lemma 5.1 anchor, raising side: the concrete Walsh coefficient
formula for the direction-`i` raising operator (`lem:raise`,
`manuscript.tex:1179-1191`; `eq:raise` = (45), `manuscript.tex:1182`). -/

open MeasureTheory
open scoped BigOperators
open Manhattan Manhattan.Glue

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Glue.lemma_raise_concrete_raising (p : Fin 2 → ℝ) (i : Fin 2)
    (T : Finset LineIndex) (x : WalshL2) :
    inner ℂ (walshL2 T) (walshRaiseDir p i x) =
      if originLine i ∈ T then
        (2 : ℂ)⁻¹ *
          (Complex.exp (Complex.I * p i) *
              inner ℂ (walshL2 (translateWalshIndex (-Operator.axisVector i)
                (T.erase (originLine i)))) x -
            Complex.exp (-Complex.I * p i) *
              inner ℂ (walshL2 (translateWalshIndex (Operator.axisVector i)
                (T.erase (originLine i)))) x)
      else 0
-- FROZEN-STATEMENT-END
:= Manhattan.Glue.inner_walshL2_walshRaiseDir p i T x
