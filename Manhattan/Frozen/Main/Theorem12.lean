import Manhattan.Model.Theorem12
import Manhattan.Glue.SectorEnergy

/-! Theorem 1.2: the annealed Green-function bound. -/

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Main.theorem_1_2 : Manhattan.AnnealedGreenBound
-- FROZEN-STATEMENT-END
:= Manhattan.Glue.theorem_1_2_proved_of_exists
    Manhattan.Glue.exists_concreteSectorEnergyBound
