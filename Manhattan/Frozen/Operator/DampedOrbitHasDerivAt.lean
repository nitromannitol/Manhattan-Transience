module

public import Manhattan.Library

@[expose] public section

/-! Frozen proved semigroup statement. -/

noncomputable section

open ComplexConjugate InnerProductSpace MeasureTheory NormedSpace RCLike
open scoped ComplexConjugate InnerProduct

universe u_1

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Operator.dampedOrbit_hasDerivAt : ∀ {E : Type u_1} [_inst : NormedAddCommGroup E]
  [_inst_1 : InnerProductSpace ℂ E] [CompleteSpace E] (G : E →L[ℂ] E) (lambda t : ℝ) (u : E),
  HasDerivAt (Manhattan.Operator.dampedOrbit G lambda u)
    (-(Manhattan.Operator.resolventOperator G lambda) (Manhattan.Operator.dampedOrbit G lambda u t)) t
-- FROZEN-STATEMENT-END
:= @LatticeProb.Analysis.dampedOrbit_hasDerivAt
