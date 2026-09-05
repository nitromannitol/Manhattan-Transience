import Manhattan.Operator.Fourier

/-! Frozen proved Fourier/fiber statement. -/

noncomputable section

open ComplexConjugate InnerProductSpace MeasureTheory RCLike UnitAddTorus
open scoped BigOperators ComplexConjugate InnerProduct

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Operator.positionFourier_single : ∀ (z : Manhattan.Operator.Lattice),
  Manhattan.Operator.positionFourier (lp.single 2 z 1) = UnitAddTorus.mFourierLp 2 z
-- FROZEN-STATEMENT-END
:= @Manhattan.Operator.positionFourier_single
