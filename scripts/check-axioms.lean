import CORALean
import CORALean.Examples.API
import CORALean.Examples.Bench.Registry
import CORALean.Examples.BenchFlint
import CORALean.Global.Float.Instances.Flint.API
import CORALean.Examples.Oracle.Run
import CORALean.Examples.Oracle.Ops.Reach
import CORALean.Examples.Oracle.Ops.FromRound
import CORALean.Examples.Oracle.Ops.ZonotopeOps
import CORALean.Examples.Oracle.Ops.Enclosure
import CORALean.Examples.Bench.OracleUnsound

/-!
# No library result rests on the bench's false axiom, and `trustedFlint` stays opt-in

Run by `scripts/check-axioms.sh` through `lake env lean`, against a built tree
— importing `Examples.BenchFlint` here needs no FLINT, since `lake env lean`
only elaborates, never links. `CORALean.Examples.Bench.NearestUnsound` assumes
`nearestUnsound`, FALSE by design, so that the unchanged library runs on
round-to-nearest as CORA does. A false axiom taints exactly the declarations
whose proof terms reach it, and `Lean.collectAxioms` is what says which those
are. `CORALean.Global.Float.Instances.Flint` assumes `trustedFlint` instead,
true but opt-in: the same sweep says whether anything outside that backend and
its bench reaches it, whether or not the axiom itself is true. Eight questions:

1. Are `trustedHardware`, `nearestUnsound` and `trustedFlint` the only axioms
   any `CORALean` module declares?
2. Do the library's headline guarantees, named below, avoid `nearestUnsound`?
3. Does any declaration of any `CORALean` module outside `Examples/Bench/` reach
   it? The sweep reads the axiom sets Lean stored in each olean: a lookup each.
4. Do the two instantiations in `NearestUnsound.Tainted` reach it? The positive
   control: a check that cannot see a taint would pass 2 and 3 vacuously.
5. Does any declaration of any `CORALean` module outside `Flint/` and
   `Examples/BenchFlint` reach `trustedFlint`? The same sweep as 3, for the
   opt-in backend, over the whole tree rather than only outside the bench,
   since `Flint` is not itself part of the bench.
6. Does `BenchFlint.reachFloat_outer_flint` reach `trustedFlint`? The positive
   control 4 is for `nearestUnsound`, here for `trustedFlint`.

7. Does anything `lake exe oracle` runs, by entry declaration, reach `nearestUnsound` or
   `trustedFlint`? Its modules are imported here, not the root `Examples/Oracle.lean`, whose `main`
   would clash with the bench's; `Oracle.lean`'s `main` is `run sounds`, so `run` and `sounds`
   cover it. Question 3 sweeps these modules too, but a by-name list says what the executable is.
8. Does `Bench.OracleUnsound.dtypes` reach `nearestUnsound`? The positive control for 7: the
   unsound executable is the same code with one more dtype, so a check that cannot see that
   dtype's taint would pass 7 vacuously.

Every failure is an error, so `lean` exits nonzero.
-/

open Lean Elab Command

/-- The false axiom of the bench's round-to-nearest baseline. -/
def unsoundAxiom : Name := `CORALean.Bench.nearestUnsound

/-- What the optional FLINT backend assumes: true, unlike `unsoundAxiom`, but opt-in
the same way -- see `Global/Float/Instances/Flint/Definitions/Axioms.lean`. -/
def flintAxiom : Name := `CORALean.Float.Flint.trustedFlint

/-- The whole of what CORALean assumes: the hardware, true; the baseline, false;
the optional FLINT backend, true but opt-in. -/
def allowedAxioms : Array Name :=
  #[`CORALean.Float.Binary64.trustedHardware, unsoundAxiom, flintAxiom]

/-- The guarantees a reader of the paper relies on, by their full names. -/
def headlineTheorems : Array Name := #[
  `CORALean.LinearSys.reachWrappingFreeFloat_outer,
  `CORALean.LinearSys.reachFloat_outer,
  `CORALean.LinearSys.reachFloat_timePoint_outer,
  `CORALean.LinearSys.reachFloatInput_outer,
  `CORALean.LinearSys.reachFloatInput_timePoint_outer,
  `CORALean.LinearSys.reachWrappingFreeFloatInput_outer,
  `CORALean.LinearSys.reach_outer,
  `CORALean.LinearSys.holds_of_check,
  `CORALean.LinearSys.holds_of_check_wrappingFree,
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

/-- The positive control for `trustedFlint`: `reachFloat_outer` at `Flint 53`. -/
def flintTheorems : Array Name := #[`CORALean.Bench.reachFloat_outer_flint]

/-- What `lake exe oracle` runs, by entry: `main` is `run sounds`, `run` loops on `respond`,
which is `handleRequest` and so `handleOp` and one handler per op. -/
def oracleEntries : Array Name := #[
  `CORALean.Oracle.run, `CORALean.Oracle.respond, `CORALean.Oracle.handleRequest,
  `CORALean.Oracle.handleOp, `CORALean.Oracle.sounds,
  `CORALean.Oracle.handleFrom, `CORALean.Oracle.handleRoundTo, `CORALean.Oracle.handleMtimes,
  `CORALean.Oracle.handleMtimesInterval, `CORALean.Oracle.handlePlus,
  `CORALean.Oracle.handlePlusBox, `CORALean.Oracle.handleLinComb, `CORALean.Oracle.handleReduce,
  `CORALean.Oracle.handleInterval, `CORALean.Oracle.handleEnclosure,
  `CORALean.Oracle.handleLinearSysReach]

/-- The positive control for `oracleEntries`: the unsound oracle's dtypes, which add `nearest`. -/
def oracleUnsoundTaints : Array Name := #[`CORALean.Bench.OracleUnsound.dtypes]

/-- Whether module `m` is CORALean's, and whether it is library code, outside
the bench -- `BenchFlint`/`BenchFlintMain` count as bench here too, even
though they sit beside `Examples/Bench/` rather than inside it (so that file
stays untouched): `dispatchFlint` calls the shared `runAt`, which reaches
`nearestUnsound` whenever `args.experiment = "nn-float32"`, exactly as
`Registry.lean`'s own `dispatch` does, and that is the bench harness's
intended baseline row, not a leak into the library. -/
def isOurs (m : Name) : Bool := (`CORALean).isPrefixOf m
def isLibraryModule (m : Name) : Bool :=
  isOurs m && !(`CORALean.Examples.Bench).isPrefixOf m &&
    m != `CORALean.Examples.BenchFlint && m != `CORALean.Examples.BenchFlintMain

/-- Whether `m` is the FLINT backend or its bench, the only modules that may
reach `trustedFlint` -- `Flint/` sits under `Global/Float/Instances`, not
under `Examples/Bench/`, so this is not `isLibraryModule`'s exclusion. -/
def isFlintAllowed (m : Name) : Bool :=
  (`CORALean.Global.Float.Instances.Flint).isPrefixOf m ||
    m == `CORALean.Examples.BenchFlint || m == `CORALean.Examples.BenchFlintMain

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
  unless declared.contains flintAxiom do
    logError m!"{flintAxiom} not found — renamed? update scripts/check-axioms.lean"
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
  -- 5. the sweep, for `trustedFlint`: every declaration of every module outside
  -- the FLINT backend and its bench, over the whole tree rather than only
  -- outside `Examples/Bench/`, since `Flint/` sits elsewhere
  let mut sweptFlint : Nat := 0
  let mut reachedFlint : Array Name := #[]
  for (n, _) in env.constants.map₁.toList do
    unless ((moduleOf n).map isOurs).getD false do continue
    if ((moduleOf n).map isFlintAllowed).getD false then continue
    sweptFlint := sweptFlint + 1
    if (← collectAxioms n).contains flintAxiom then reachedFlint := reachedFlint.push n
  if reachedFlint.isEmpty then
    logInfo m!"ok      {sweptFlint} declarations outside Flint/BenchFlint: none reaches {flintAxiom}"
  else
    logError m!"{reachedFlint.size} declarations reach {flintAxiom} outside the opt-in backend: \
      {reachedFlint.toList.take 20}"
  -- 6. the positive control for `trustedFlint`
  for n in flintTheorems do
    unless env.contains n do
      logError m!"{n}: not found — the positive control is missing"
      continue
    if (← collectAxioms n).contains flintAxiom then
      logInfo m!"ok      {n} reaches {flintAxiom}, as it must"
    else
      logError m!"{n} should reach {flintAxiom} and does not — the check sees no reach"
  -- 7. the oracle, by entry declaration: neither the false axiom nor FLINT
  for n in oracleEntries do
    unless env.contains n do
      logError m!"{n}: not found — renamed? update scripts/check-axioms.lean"
      continue
    let axs ← collectAxioms n
    if axs.contains unsoundAxiom || axs.contains flintAxiom then
      logError m!"TAINTED oracle entry {n} depends on {unsoundAxiom} or {flintAxiom}"
    else logInfo m!"ok      oracle {n}: {axs}"
  -- 8. the positive control for 7
  for n in oracleUnsoundTaints do
    unless env.contains n do
      logError m!"{n}: not found — the positive control is missing"
      continue
    if (← collectAxioms n).contains unsoundAxiom then
      logInfo m!"ok      {n} reaches {unsoundAxiom}, as it must"
    else
      logError m!"{n} should reach {unsoundAxiom} and does not — the oracle check sees no taint"
