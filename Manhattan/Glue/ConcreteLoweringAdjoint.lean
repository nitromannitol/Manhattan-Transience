import Manhattan.Glue.ConcreteRaising
import Manhattan.Glue.ConcreteLoweringFourier

/-!
# The lowering coefficient as the adjoint of the raising operator

The operator form of Lemma 5.1 is
`concreteFiberA p = walshRaise p - walshLower p` and
`walshLower p = (walshRaise p)†`
(`Manhattan/Glue/ConcreteRaising.lean`).  This file records that the
coefficient map `Manhattan.Glue.loweringCoefficient` used for (D1), (D2a) and
(D2b) is exactly the adjoint pairing against that raising operator, so the two
files describe the same `D` and `D*`.

Paper: `manuscript.tex:733-740`, `manuscript.tex:1176-1205`.
-/

open ComplexConjugate InnerProductSpace

namespace Manhattan.Glue

noncomputable section

/-- The lowering coefficient, expanded through operator splitting.
The first term is the adjoint pairing against the raising operator; the second
is the contribution of the lowering part of `A_p` on the test character. -/
theorem loweringCoefficient_eq_walshRaise (p : Fin 2 → ℝ) (x : WalshL2)
    (S : Finset LineIndex) :
    loweringCoefficient p x S =
      inner ℂ (walshRaise p (walshL2 S)) x -
        inner ℂ (walshL2 S) (walshRaise p x) := by
  rw [loweringCoefficient, concreteFiberA_eq_walshRaise_sub_walshLower,
    ContinuousLinearMap.sub_apply, inner_sub_left,
    walshLower_eq_adjoint_walshRaise, ContinuousLinearMap.adjoint_inner_left]

/-- `D*` is the adjoint of `D`: whenever the raising image of `x` has no
component along the test index `S`, the lowering coefficient at `S` is exactly
`⟪D (walshL2 S), x⟫`. -/
theorem loweringCoefficient_eq_inner_walshRaise (p : Fin 2 → ℝ) (x : WalshL2)
    (S : Finset LineIndex) (h : inner ℂ (walshL2 S) (walshRaise p x) = 0) :
    loweringCoefficient p x S = inner ℂ (walshRaise p (walshL2 S)) x := by
  rw [loweringCoefficient_eq_walshRaise, h, sub_zero]

end

end Manhattan.Glue
