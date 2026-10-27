module

public import Mathlib.Logic.Basic
public import CORALean.Global.StepOf

@[expose] public section

/-!
# CORA's `reduceUnderApprox` never runs its legacy methods when it should

In `@zonotope/reduceUnderApprox.m` (l. 76-113) the `end` at l. 101 closes the chain
`if strcmp(method,'sadraddini') ... elseif strcmp(method,'cluster') ... end` early, so the
`elseif` branches of the LEGACY methods (`'boxLP'`, `'boxWetzlinger'`, `'boxNLP'`, l. 103-109)
attach to the outer test `if n*order < nrOfGens` (reduction needed). Needed: only the inner chain
runs, no case matches a legacy name, and the set is returned unreduced. Not needed: a legacy
method runs on a zonotope within the order (it shrinks it needlessly or fails). Only the control
flow is modelled (read from the source, not run).

## Inputs
* `m` – legacy method

## Hypotheses
* `hm` – method is legacy

## Conclusion
* CORA's dispatch is the reverse of the intended nesting
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

namespace ReduceUnderApproxDispatch


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- The method names of `reduceUnderApprox` (old names identify with the new ones). -/
@[step_of cora_legacy_dispatch]
inductive step_Method
  | sadraddini | yang | raghuraman | kochdumper | scale | boxCone | nlp | cluster
  | boxLP | boxWetzlinger | boxNLP
  deriving DecidableEq

/-- The methods CORA's comment calls `LEGACY`. -/
@[step_of cora_legacy_dispatch]
def step_isLegacy : step_Method → Bool
  | .boxLP | .boxWetzlinger | .boxNLP => true
  | _ => false

/-- What a call does: returns the set unchanged, or runs the method's routine. -/
@[step_of cora_legacy_dispatch]
inductive step_Outcome
  | unchanged
  | runs (m : step_Method)
  deriving DecidableEq

/-- The nesting as written: the legacy `elseif`s hang on `if n*order < nrOfGens`. -/
@[step_of cora_legacy_dispatch]
def step_cora (needed : Bool) (m : step_Method) : step_Outcome :=
  if needed then
    if step_isLegacy m then .unchanged else .runs m
  else
    if step_isLegacy m then .runs m else .unchanged

/-- The nesting as intended: all methods inside the test, `else return`. -/
@[step_of cora_legacy_dispatch]
def step_intended (needed : Bool) (m : step_Method) : step_Outcome :=
  if needed then .runs m else .unchanged


-- =======================================  MAIN THEOREM  ======================================= --

/-- For a legacy method CORA does nothing where reduction is needed and runs the routine where
it is not, both the reverse of the intended nesting. -/
theorem cora_legacy_dispatch (m : step_Method) (hm : step_isLegacy m = true) :
    (step_cora true m = .unchanged ∧ step_intended true m = .runs m) ∧
      (step_cora false m = .runs m ∧ step_intended false m = .unchanged) := by
  simp [step_cora, step_intended, hm]

end ReduceUnderApproxDispatch

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
