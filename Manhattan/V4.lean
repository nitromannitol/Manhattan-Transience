import Manhattan.V4.Variational
import Manhattan.V4.EvenMajorant
import Manhattan.V4.Parity
import Manhattan.V4.ParityIntegral
import Manhattan.V4.LogScale
import Manhattan.V4.ScalarMinimization
import Manhattan.V4.Energy.Weight
import Manhattan.V4.Energy.BetaIntegral
import Manhattan.V4.Energy.DegreeOne
import Manhattan.V4.Energy.Move1
import Manhattan.V4.Energy.Witnesses
import Manhattan.V4.CompetitorEnergy
import Manhattan.V4.OperatorEstimate
import Manhattan.V4.MixedBridge
import Manhattan.V4.MixedSector
import Manhattan.V4.TwoRow
import Manhattan.V4.Sectors
import Manhattan.V4.Frequency.Profile
import Manhattan.V4.Frequency.FixedFrequency
import Manhattan.V4.Frequency.Integration
import Manhattan.V4.Frequency.Witness
import Manhattan.V4.Frequency.Uniform
import Manhattan.V4.AssemblyWitnesses
import Manhattan.V4.MixedBridgeWitnesses
import Manhattan.V4.PeriodicProfile
import Manhattan.V4.Move1Cost
import Manhattan.V4.Move1
import Manhattan.V4.Move2Supply
import Manhattan.V4.SupplyWitnesses

/-!
# Version 4

The second, independent route to Theorem 1.1.  `Manhattan.V4.theorem_1_1_v4`
proves the statement of `Manhattan.Frozen.Main.theorem_1_1` from the Version 4
Move 1 / Move 2 / Move 3 chain; the two developments share the model, the Walsh
layer and the operator layer, and diverge at the competitor construction.

Nothing in this subtree carries a manifest node, and nothing here is mirrored
under `Manhattan/Frozen/`.
-/
