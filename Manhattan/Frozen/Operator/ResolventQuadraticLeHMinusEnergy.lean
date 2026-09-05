import Manhattan.Operator.Variational

/-! Frozen proved operator statement. -/

noncomputable section


universe u_1

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Operator.resolventQuadratic_le_hMinusEnergy : ∀ {E : Type u_1}
  [_inst : NormedAddCommGroup E] [_inst_1 : InnerProductSpace ℂ E] [_inst_2 : CompleteSpace E]
  (P : Manhattan.Operator.DissipativeSkewPair E) {lambda : ℝ} (hlambda : 0 < lambda) (V : E),
  P.resolventQuadratic hlambda V ≤ P.hMinusEnergy hlambda V
-- FROZEN-STATEMENT-END
:= @Manhattan.Operator.DissipativeSkewPair.resolventQuadratic_le_hMinusEnergy
