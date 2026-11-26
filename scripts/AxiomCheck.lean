import CausalInference

/-!
# Axiom check

Run with `lake env lean scripts/AxiomCheck.lean` from the repository root.

Walks every constant whose defining module is `libRoot` or lies below it, computes the axioms it
depends on with `Lean.collectAxioms` (the mechanism behind `#print axioms`), and fails listing
every constant that depends on an axiom outside `allowedAxioms`. This catches `sorryAx`, any
axiom declared in the library itself, and the compiler trust axioms: in Lean v4.36.0 each use of
`native_decide` adds its own auxiliary axiom (named `..._native.native_decide.ax_...`), and
older toolchains use `Lean.ofReduceBool` and `Lean.trustCompiler`; all of these lie outside
`allowedAxioms`.

This file is not a module, so it sees the private declarations and theorem bodies of the module
system files it imports.
-/

open Lean Elab Command

/-- Root of the module names whose constants are checked. -/
def libRoot : Name := `CausalInference

/-- The axioms a library constant may depend on. -/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

run_cmd do
  let env ← getEnv
  let modNames := env.header.moduleNames
  let mut checked := 0
  let mut theorems := 0
  let mut seen : NameSet := {}
  let mut bad : Array (Name × Array Name) := #[]
  for (c, info) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? c | continue
    unless libRoot.isPrefixOf modNames[idx.toNat]! do continue
    checked := checked + 1
    if info matches .thmInfo _ then theorems := theorems + 1
    let axs ← collectAxioms c
    seen := axs.foldl NameSet.insert seen
    let extra := axs.filter (!allowedAxioms.contains ·)
    unless extra.isEmpty do bad := bad.push (c, extra)
  let seenList := seen.toList.map toString |>.toArray.qsort (· < ·) |>.toList
  logInfo m!"checked {checked} constants ({theorems} theorems); axioms seen: \
    {", ".intercalate seenList}"
  if checked == 0 then
    throwError "no constants found in modules under {libRoot}"
  unless bad.isEmpty do
    let lines := bad.qsort (fun a b => a.1.toString < b.1.toString) |>.map
      fun (c, axs) => s!"  {c}: {axs}"
    throwError "{bad.size} constants depend on disallowed axioms:\n{"\n".intercalate lines.toList}"
