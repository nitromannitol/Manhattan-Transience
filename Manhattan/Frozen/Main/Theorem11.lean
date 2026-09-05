import Manhattan.Model.MainTheorem
import Manhattan.Glue.SectorEnergy

/-! Theorem 1.1: quenched return summability at every site. -/

open Filter MeasureTheory
open scoped ENNReal

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Main.theorem_1_1 :
    ∀ᵐ omega ∂Manhattan.environmentLaw,
      ∀ x : Manhattan.Site, Manhattan.discreteGreen omega x < ∞
-- FROZEN-STATEMENT-END
:= Manhattan.Glue.theorem_1_1_proved_of_exists
    Manhattan.Glue.exists_concreteSectorEnergyBound
