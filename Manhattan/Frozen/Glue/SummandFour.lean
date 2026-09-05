import Manhattan.Glue.SummandFourAssembly

/-! Frozen anchor: summand four of the four-sector objective
`eq:E` = (22) (`manuscript.tex:765-772`) at the concrete competitor. -/

open Manhattan Manhattan.Glue

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Glue.summand_four_bound :
    ∃ C : ℝ, 0 ≤ C ∧ SummandFourBound C
-- FROZEN-STATEMENT-END
:= Manhattan.Glue.summandFourBound_proved
