import Mathlib.Logic.Basic

/-!
# CORA's `reduceUnderApprox` never runs its legacy methods when it should

In `@zonotope/reduceUnderApprox.m` (l. 76-113) the `end` at l. 101 closes the chain
`if strcmp(method,'sadraddini') ... elseif strcmp(method,'cluster') ... end` early, so the
`elseif` branches of the LEGACY methods `'boxLP'`/`'linProg'`, `'boxWetzlinger'`/`'wetzlinger'`
and `'boxNLP'` (l. 103-109) attach to the outer test `if n*order < nrOfGens` (reduction needed):

* reduction needed: the outer test is true, so only the inner chain runs; no case of it matches
  a legacy name and the (compacted) set is returned unreduced;
* reduction not needed: the outer test is false, so the legacy `elseif`s are tried: a legacy
  method runs its `aux_reduceUnderApprox...` on a zonotope within the order (it shrinks it
  needlessly or fails when asked for `floor(order*n-n)` generators of fewer), the others hit
  `else return`.

This file models the control flow only (read from the source, not run): which routine the code
reaches for a given `needed` and method, against what the nesting was meant to do.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

namespace ReduceUnderApproxDispatch


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The method names of `reduceUnderApprox` (old names identify with the new ones). -/
inductive aux_Method
  | sadraddini | yang | raghuraman | kochdumper | scale | boxCone | nlp | cluster
  | boxLP | boxWetzlinger | boxNLP
  deriving DecidableEq

/-- The methods CORA's comment calls `LEGACY`. -/
def aux_isLegacy : aux_Method → Bool
  | .boxLP | .boxWetzlinger | .boxNLP => true
  | _ => false

/-- What a call does: returns the set unchanged, or runs the method's routine. -/
inductive aux_Outcome
  | unchanged
  | runs (m : aux_Method)
  deriving DecidableEq

/-- The nesting as written: the legacy `elseif`s hang on `if n*order < nrOfGens`. -/
def aux_cora (needed : Bool) (m : aux_Method) : aux_Outcome :=
  if needed then
    if aux_isLegacy m then .unchanged else .runs m
  else
    if aux_isLegacy m then .runs m else .unchanged

/-- The nesting as intended: all methods inside the test, `else return`. -/
def aux_intended (needed : Bool) (m : aux_Method) : aux_Outcome :=
  if needed then .runs m else .unchanged


-- =======================================  MAIN THEOREM  ======================================= --

/-- For a legacy method CORA does nothing where reduction is needed and runs the routine where
it is not, both the reverse of the intended nesting. -/
theorem cora_legacy_dispatch (m : aux_Method) (hm : aux_isLegacy m = true) :
    (aux_cora true m = .unchanged ∧ aux_intended true m = .runs m) ∧
      (aux_cora false m = .runs m ∧ aux_intended false m = .unchanged) := by
  simp [aux_cora, aux_intended, hm]

end ReduceUnderApproxDispatch

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
