import Manhattan.Glue.SummandsMixed

/-! Frozen anchor: summand two of the four-sector objective
`eq:E` = (22) (`manuscript.tex:765-772`) at the concrete competitor. -/

open Manhattan Manhattan.Glue

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Glue.summand_two_bound :
    ∃ C : ℝ, 0 ≤ C ∧ SummandTwoBound C
-- FROZEN-STATEMENT-END
:= Manhattan.Glue.summandTwoBound_proved
