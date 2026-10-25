module

public import Manhattan.Estimates.PropositionFiveTwo

@[expose] public section

/-! Proposition 4.2 in the explicit degree-three vocabulary. -/

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Estimates.proposition_key (K rho : ℝ) :
    Manhattan.Estimates.PropositionFiveTwoClaim K rho
-- FROZEN-STATEMENT-END
:= Manhattan.Estimates.propositionFiveTwoClaim_proved K rho
