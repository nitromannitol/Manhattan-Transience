module

public import Manhattan.V4.Variational
public import Manhattan.V4.EvenMajorant
public import Manhattan.V4.Parity
public import Manhattan.V4.ParityIntegral
public import Manhattan.V4.LogScale
public import Manhattan.V4.ScalarMinimization
public import Manhattan.V4.Energy.Weight
public import Manhattan.V4.Energy.BetaIntegral
public import Manhattan.V4.Energy.DegreeOne
public import Manhattan.V4.Energy.Move1
public import Manhattan.V4.Energy.Witnesses
public import Manhattan.V4.CompetitorEnergy
public import Manhattan.V4.OperatorEstimate
public import Manhattan.V4.MixedBridge
public import Manhattan.V4.MixedSector
public import Manhattan.V4.TwoRow
public import Manhattan.V4.Sectors
public import Manhattan.V4.Frequency.Profile
public import Manhattan.V4.Frequency.FixedFrequency
public import Manhattan.V4.Frequency.Integration
public import Manhattan.V4.Frequency.Witness
public import Manhattan.V4.Frequency.Uniform
public import Manhattan.V4.AssemblyWitnesses
public import Manhattan.V4.MixedBridgeWitnesses
public import Manhattan.V4.PeriodicProfile
public import Manhattan.V4.Move1Cost
public import Manhattan.V4.Move1
public import Manhattan.V4.Move2Supply
public import Manhattan.V4.SupplyWitnesses

@[expose] public section

/-!
# Version 4

The second, independent route to Theorem 1.1.  `Manhattan.V4.theorem_1_1_v4`
proves the statement of `Manhattan.Frozen.Main.theorem_1_1` from the Version 4
Move 1 / Move 2 / Move 3 chain; the two developments share the model, the Walsh
layer and the operator layer, and diverge at the competitor construction.

Nothing in this subtree carries a manifest node, and nothing here is mirrored
under `Manhattan/Frozen/`.
-/
