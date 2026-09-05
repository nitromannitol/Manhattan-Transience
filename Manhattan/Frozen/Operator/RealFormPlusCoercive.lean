import Manhattan.Operator.Variational

/-! Frozen proved operator statement. -/

noncomputable section


universe u_1

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Operator.realForm_plus_coercive : ∀ {E : Type u_1} [_inst : NormedAddCommGroup E]
  [_inst_1 : InnerProductSpace ℂ E] [_inst_2 : CompleteSpace E] (P : Manhattan.Operator.DissipativeSkewPair E)
  {lambda : ℝ}, 0 < lambda → IsCoercive (Manhattan.Operator.DissipativeSkewPair.realForm (P.plus lambda))
-- FROZEN-STATEMENT-END
:= @Manhattan.Operator.DissipativeSkewPair.realForm_plus_coercive
