import Manhattan.Estimates.LemmaFourTwoSuccessor

/-! Corrected Lemma 4.1 in the explicit normalized-torus vocabulary. -/

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Estimates.lemma_one_coin (K rho : ℝ) :
    Manhattan.Estimates.LemmaFourTwoSuccessorClaim K rho
-- FROZEN-STATEMENT-END
:= Manhattan.Estimates.lemmaFourTwoSuccessorClaim_proved K rho
