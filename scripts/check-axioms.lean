import CORALean
import CORALean.Examples.API
import CORALean.Examples.Bench

/-!
# No library result rests on the bench's false axiom

Run by `scripts/check-axioms.sh` through `lake env lean`, against a built tree.
`CORALean.Examples.Bench.NearestUnsound` assumes `nearestUnsound`, FALSE by
design, so that the unchanged library runs on round-to-nearest as CORA does. A
false axiom taints exactly the declarations whose proof terms reach it, and
`Lean.collectAxioms` is what says which those are. Four questions:

1. Are `trustedHardware` and `nearestUnsound` the only axioms any `CORALean`
   module declares?
2. Do the library's headline guarantees, named below, avoid `nearestUnsound`?
3. Does any declaration of any `CORALean` module outside `Examples/Bench/` reach
   it? The sweep reads the axiom sets Lean stored in each olean: a lookup each.
4. Do the two instantiations in `NearestUnsound.Tainted` reach it? The positive
   control: a check that cannot see a taint would pass 2 and 3 vacuously.

Every failure is an error, so `lean` exits nonzero.
-/

open Lean Elab Command

/-- The false axiom of the bench's round-to-nearest baseline. -/
def unsoundAxiom : Name := `CORALean.Bench.nearestUnsound

/-- The whole of what CORALean assumes: the hardware, true, and the baseline, false. -/
def allowedAxioms : Array Name := #[`CORALean.Float.Binary64.trustedHardware, unsoundAxiom]

/-- The guarantees a reader of the paper relies on, by their full names. -/
def headlineTheorems : Array Name := #[
  `CORALean.LinearSys.reachWrappingFreeFloat_outer,
  `CORALean.LinearSys.reachFloat_outer,
  `CORALean.LinearSys.reachFloat_timePoint_outer,
  `CORALean.LinearSys.holds_of_check,
  `CORALean.Reach.holds_of_check,
  `CORALean.Specification.check_sound,
  `CORALean.NeuralNetwork.enclose_outer,
  `CORALean.NeuralNetwork.Sound.enclose_outer,
  `CORALean.NeuralNetwork.holds_of_enclose,
  `CORALean.NeuralNetwork.holds_of_check,
  `CORALean.Float.Zonotope.mtimesIntervalMat_outer,
  `CORALean.Float.Interval.mtimesIntervalMat_outer,
  `CORALean.Float.instSoundFloatArithmeticFloat]

/-- The positive controls: `reachFloat_outer` at `NearestFloat` and `NearestDyadic 24`. -/
def taintedTheorems : Array Name := #[
  `CORALean.Bench.NearestUnsound.reachFloat_outer_nearestFloat,
  `CORALean.Bench.NearestUnsound.reachFloat_outer_nearestDyadic]

/-- Whether module `m` is CORALean's, and whether it is library code, outside the bench. -/
def isOurs (m : Name) : Bool := (`CORALean).isPrefixOf m
def isLibraryModule (m : Name) : Bool := isOurs m && !(`CORALean.Examples.Bench).isPrefixOf m

run_cmd do
  let env ← getEnv
  let modules := env.header.moduleNames                  -- hoisted: `header` is not free
  let moduleOf (n : Name) : Option Name := (env.getModuleIdxFor? n).map (modules[·.toNat]!)
  -- 1. every axiom a CORALean module declares, found rather than listed
  let declared := env.constants.fold (init := #[]) fun acc n ci =>
    if ci matches .axiomInfo _ && ((moduleOf n).map isOurs).getD false then acc.push n else acc
  logInfo m!"check-axioms: CORALean declares the axioms {declared}"
  for n in declared do
    unless allowedAxioms.contains n do logError m!"{n}: an axiom nobody allowed"
  unless declared.contains unsoundAxiom do
    logError m!"{unsoundAxiom} not found — renamed? update scripts/check-axioms.lean"
  -- 2. the headline guarantees, by name
  for n in headlineTheorems do
    unless env.contains n do
      logError m!"{n}: not found — renamed? update scripts/check-axioms.lean"
      continue
    let axs ← collectAxioms n
    if axs.contains unsoundAxiom then logError m!"TAINTED {n} depends on {unsoundAxiom}"
    else logInfo m!"ok      {n}: {axs}"
  -- 3. the sweep: every declaration of every library module
  let mut swept : Nat := 0
  let mut tainted : Array Name := #[]
  for (n, _) in env.constants.map₁.toList do
    unless ((moduleOf n).map isLibraryModule).getD false do continue
    swept := swept + 1
    if (← collectAxioms n).contains unsoundAxiom then tainted := tainted.push n
  if tainted.isEmpty then
    logInfo m!"ok      {swept} library declarations outside Examples/Bench: none reaches it"
  else
    logError m!"TAINTED {tainted.size} library declarations reach {unsoundAxiom}: \
      {tainted.toList.take 20}"
  -- 4. the positive control: the taint must be visible where it is meant to be
  for n in taintedTheorems do
    unless env.contains n do
      logError m!"{n}: not found — the positive control is missing"
      continue
    if (← collectAxioms n).contains unsoundAxiom then
      logInfo m!"ok      {n} reaches {unsoundAxiom}, as it must"
    else
      logError m!"{n} should reach {unsoundAxiom} and does not — the check sees no taint"
