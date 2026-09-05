import Manhattan.Operator.Fourier

/-! Frozen proved Fourier/fiber statement. -/

noncomputable section

open ComplexConjugate InnerProductSpace MeasureTheory RCLike UnitAddTorus
open scoped BigOperators ComplexConjugate InnerProduct

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Operator.positionFourier_norm : ∀ (f : ↥Manhattan.Operator.PositionL2),
  ‖Manhattan.Operator.positionFourier f‖ = ‖f‖
-- FROZEN-STATEMENT-END
:= @Manhattan.Operator.positionFourier_norm
