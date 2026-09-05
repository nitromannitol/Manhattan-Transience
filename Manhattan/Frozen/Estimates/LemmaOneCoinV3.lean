import Manhattan.Estimates.LemmaFourTwoSuccessor

/-! Lemma 4.1 successor with explicit integral-finiteness certificates. -/

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Estimates.lemma_one_coin_v3 (K rho : ℝ) :
    Manhattan.Estimates.LemmaFourTwoSuccessorV3Claim K rho
-- FROZEN-STATEMENT-END
:= Manhattan.Estimates.lemmaFourTwoSuccessorV3Claim_proved K rho
