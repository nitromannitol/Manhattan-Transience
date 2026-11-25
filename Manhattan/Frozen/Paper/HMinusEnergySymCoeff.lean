import Manhattan.Paper.SymmetricIso

/-! Equations `eq:iso` and `eq:Hsym` (`manuscript.tex:730-732`, `:749`) for the dual
energy: a degree-`n` element `F` with symmetric coefficient `f` has
`‖F‖²_{H⁻¹} = n! ⟨f, (λ + θ(P))⁻¹ f⟩`. -/

open MeasureTheory UnitAddTorus
open Manhattan Manhattan.Glue Manhattan.Paper

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Paper.hMinusEnergy_eq_symCoeff (n : ℕ) {lam : ℝ} (hlam : 0 < lam) (p : Fin 2 → ℝ)
    (c : DegreeCoefficient n) :
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hlam
        (homogeneousWalshSynthesis n c) =
      n.factorial * RCLike.re (inner ℂ (symCoeff n (homogeneousWalshSynthesis n c))
        (orderedMultiplier n p (hInvMap hlam) (symCoeff n (homogeneousWalshSynthesis n c))))
-- FROZEN-STATEMENT-END
:= Manhattan.Paper.hMinusEnergy_eq_symCoeff n hlam p c
