import Manhattan.Operator.Variational

/-! Frozen proved operator statement. -/

noncomputable section


universe u_1

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Operator.resolventQuadratic_le : ∀ {E : Type u_1} [_inst : NormedAddCommGroup E]
  [_inst_1 : InnerProductSpace ℂ E] [_inst_2 : CompleteSpace E] (P : Manhattan.Operator.DissipativeSkewPair E)
  {lambda : ℝ} (hlambda : 0 < lambda) (V g : E),
  P.resolventQuadratic hlambda V ≤ P.hEnergy lambda g + P.hMinusEnergy hlambda (V - P.A g)
-- FROZEN-STATEMENT-END
:= @Manhattan.Operator.DissipativeSkewPair.resolventQuadratic_le
