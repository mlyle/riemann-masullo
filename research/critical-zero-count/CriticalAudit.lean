import Lean
import RiemannMasullo.Ch10_TraceSpectral.Sec3_Printed
import UnconditionalCount
open Lean Elab Command

private def auditRoot (n : Name) : CommandElabM Unit := do
  let env ← getEnv
  unless env.contains n do throwError "unknown audit root {n}"
  let axioms ← Lean.collectAxioms n
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  for ax in axioms do unless allowed.contains ax do throwError "unexpected axiom {ax} at {n}"
  let mut pending := #[n]
  let mut visited : Std.HashSet Name := {}
  let mut mods : Std.HashSet Name := {}
  let mut directSorry : Array Name := #[]
  while let some d := pending.back? do
    pending := pending.pop
    if visited.contains d then continue
    visited := visited.insert d
    let some info := env.find? d | continue
    if let some ix := env.getModuleIdxFor? d then
      mods := mods.insert (env.header.moduleNames[ix.toNat]!)
    let inType := info.type.getUsedConstants
    let inBody := if let some v := info.value? true then v.getUsedConstants else #[]
    if inType.contains ``sorryAx || inBody.contains ``sorryAx then
      directSorry := directSorry.push d
    for dep in inType ++ inBody do
      if !visited.contains dep then pending := pending.push dep
  if !directSorry.isEmpty then throwError "{n} reaches admissions at {directSorry}"
  logInfo m!"{n}: {visited.size} reached declarations across {mods.size} modules; zero direct sorryAx dependencies; kernel axioms {axioms}"

run_cmd do
  for n in [`Zeta23.riemannVonMangoldt_zeta, `Zeta23.thmA₀,
      `RiemannMasullo.verified_critical_zero_count,
      "_private.RiemannMasullo.Ch10_TraceSpectral.Sec3_Printed.0.RiemannMasullo.spectralLineJet_rational_critical_zero_count".toName,
      `RiemannMasullo.Printed.spectralLineJet_uniformBiorthogonalBound_false] do
    auditRoot n
