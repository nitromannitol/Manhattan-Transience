import Manhattan.Glue.SectorEnergy

/-! Frozen anchor for the paper's estimate `E_p(f_p,k_p) ≤ C √L`: the third
display of `eq:construction` = (25) (`manuscript.tex:785-790`) for the
four-sector objective `eq:E` = (22) (`manuscript.tex:765-772`), at the concrete
competitor of `Manhattan/Glue/Correction.lean`. The repository's shorthand for
this estimate is "(23)". -/

open Manhattan Manhattan.Glue

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Glue.sector_energy_bound :
    ∃ M : ℝ, 0 ≤ M ∧ ConcreteSectorEnergyBound M
-- FROZEN-STATEMENT-END
:= Manhattan.Glue.exists_concreteSectorEnergyBound
