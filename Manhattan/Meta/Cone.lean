/-
Transitive dependency cones.

`#print axioms` tells us which axioms a theorem rests on, but not which
*declarations* its proof actually uses.  That second question is the one an
audit needs: a lemma flagged as weak matters only if the main theorem's proof
term reaches it.  This file walks the transitive closure of the constants
occurring in a declaration's type and value, and reports membership.
-/
import Manhattan.V4.Move2Supply
import Manhattan.V4.Energy.Move1
import Manhattan.V4.Energy.Witnesses
import Manhattan.Frozen.Main.Theorem11
import Lean

open Lean Elab Command

namespace Manhattan.Meta

/-- Every constant reachable from `start` through types and proof terms. -/
partial def collectCone (env : Lean.Environment) : List Name → NameSet → NameSet
  | [], acc => acc
  | n :: rest, acc =>
    if acc.contains n then collectCone env rest acc
    else
      let acc := acc.insert n
      match env.find? n with
      | none => collectCone env rest acc
      | some ci =>
        let deps := ci.type.getUsedConstants ++
          (match ci.value? with
            | some v => v.getUsedConstants
            | none => #[])
        collectCone env (deps.toList ++ rest) acc

/-- `#cone_size foo` reports how many constants `foo`'s proof reaches. -/
elab "#cone_size " tgt:ident : command => do
  let env ← getEnv
  let tgtN ← liftCoreM <| realizeGlobalConstNoOverload tgt
  let cone := collectCone env [tgtN] {}
  logInfo m!"{tgtN}: cone has {cone.size} constants"

/-- `#in_cone foo bar baz` reports, for each of `bar baz`, whether the proof of
`foo` reaches it.  This is the audit question: a defect outside the cone cannot
affect `foo`. -/
elab "#in_cone " tgt:ident ppSpace needles:(ident)+ : command => do
  let env ← getEnv
  let tgtN ← liftCoreM <| realizeGlobalConstNoOverload tgt
  let cone := collectCone env [tgtN] {}
  let mut msg := m!"cone of {tgtN} ({cone.size} constants):"
  for nd in needles do
    let n ← liftCoreM <| realizeGlobalConstNoOverload nd
    msg := msg ++ m!"\n  {if cone.contains n then "IN CONE     " else "not in cone "} {n}"
  logInfo msg

/-- `#unreachable_from foo bar` lists every declaration in the `Manhattan`
namespace that neither `foo` nor `bar` reaches.  Those are the parts of the
development that no main result depends on: scaffolding, superseded
attempts, and documentary witnesses. -/
elab "#unreachable_from " roots:(ident)+ : command => do
  let env ← getEnv
  let mut cone : NameSet := {}
  for r in roots do
    let n ← liftCoreM <| realizeGlobalConstNoOverload r
    cone := collectCone env [n] cone
  let mut dead : Array Name := #[]
  for (n, _) in env.constants.toList do
    if n.getRoot == `Manhattan && !cone.contains n && !n.isInternal then
      dead := dead.push n
  let sorted := dead.qsort (fun a b => a.toString < b.toString)
  let mut msg := m!"{sorted.size} Manhattan declarations are unreachable from the roots"
  for n in sorted do
    msg := msg ++ m!"\n  {n}"
  logInfo msg

end Manhattan.Meta

/-! ### The audit query

The 2026-09 audit of the Version 4 energy files flagged `move1_energy_le` for
resting on a Bochner integral that is the junk value `0` when its integrand is
non-measurable, and `nonvacuity_effectiveEnergy_le` for discharging a
hypothesis by `le_refl`.  Both objections are about whether those statements
say anything, so they matter only if the main theorem's proof reaches them.
-/

#in_cone Manhattan.V4.theorem_1_1_v4
  Manhattan.V4.Energy.move1_energy_le
  Manhattan.V4.Energy.effectiveEnergy_le
  Manhattan.V4.Energy.nonvacuity_effectiveEnergy_le

#cone_size Manhattan.V4.theorem_1_1_v4
#cone_size Manhattan.Frozen.Main.theorem_1_1
