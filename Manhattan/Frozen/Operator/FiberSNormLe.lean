import Manhattan.Operator.Fourier

/-! Frozen proved Fourier/fiber statement. -/

noncomputable section

open ComplexConjugate InnerProductSpace MeasureTheory RCLike UnitAddTorus
open scoped BigOperators ComplexConjugate InnerProduct

universe u_1

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Operator.fiberS_norm_le : ∀ {E : Type u_1} [_inst : NormedAddCommGroup E]
  [_inst_1 : InnerProductSpace ℂ E] [_inst_2 : CompleteSpace E] (D : Manhattan.Operator.FiberEnvironment E)
  (p : Fin 2 → ℝ), ‖D.fiberS p‖ ≤ 4
-- FROZEN-STATEMENT-END
:= @Manhattan.Operator.FiberEnvironment.fiberS_norm_le
