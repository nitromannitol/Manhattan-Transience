import Manhattan.Glue.SummandThreeMixedBound

/-! Frozen anchor: summand three of the four-sector objective
`eq:E` = (22) (`manuscript.tex:765-772`) at the concrete competitor. -/

open Manhattan Manhattan.Glue

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Glue.summand_three_bound :
    ∃ C₃ : ℝ, 0 ≤ C₃ ∧ SummandThreeBound C₃
-- FROZEN-STATEMENT-END
:= Manhattan.Glue.summandThreeBound_proved
