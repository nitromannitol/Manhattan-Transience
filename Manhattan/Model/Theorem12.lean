import Manhattan.Model.Subordination
import Manhattan.Glue.SectorEnergy

/-!
# The annealed Green-function anchor

This is the interface supplied by the operator and estimate files.  Its statement contains both the uniform Laplace-transform bound and the
undamped finiteness conclusion exactly as Theorem 1.2 does.

Paper: `manuscript.tex:207-214`.
-/

namespace Manhattan

-- DISCHARGED: `Manhattan.Glue.theorem_1_2_proved_of_exists` applied to equation
-- (23), `Manhattan.Glue.exists_concreteSectorEnergyBound`.
-- FROZEN-STATEMENT-BEGIN
theorem theorem_1_2 : AnnealedGreenBound
-- FROZEN-STATEMENT-END
  := Manhattan.Glue.theorem_1_2_proved_of_exists
    Manhattan.Glue.exists_concreteSectorEnergyBound

end Manhattan
