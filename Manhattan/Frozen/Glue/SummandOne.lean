import Manhattan.Glue.Summands

/-! Frozen anchor: summand one of the four-sector objective
`eq:E` = (22) (`manuscript.tex:765-772`) at the concrete competitor. -/

open Manhattan Manhattan.Glue

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Glue.summand_one_bound :
    ∃ C : ℝ, 0 ≤ C ∧ SummandOneBound C
-- FROZEN-STATEMENT-END
:= Manhattan.Glue.summandOneBound_proved
