module

public import CORALean.ContSet.ContSet.ContSet

@[expose] public section

/-!
# `NonlinearARX.reachStepCora`, the output set CORA's `reach` stores for one step

CORA's `@nonlinearARX/reach.m` [1], linearize-and-reformulate branch (`otherwise`), step `k`: the
body from `linReach` (l. 139) to the output set `Y_d` (l. 147-152) sits in `try` (l. 137), and
`catch` (l. 154-155) sets `Y_d = zonotope([])`. `zonotope([])` has empty centre and generators,
which `isemptyobject` reads as the empty set. Either way l. 158 stores `Y_d` as
`timePoint.set{k}` and l. 164-166 hand it to `check`: the error is neither rethrown nor warned
about.

The computation inside `try` is abstracted to `attempt`: `some Y` when it succeeds, `none` when
any statement in it errors. Sets are `Set α`, the empty zonotope being `∅`.

## References

* [1] `contDynamics/@nonlinearARX/reach.m`, CORA, ll. 137-166.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {α : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `timePoint.set{k}`: the computed `Y_d`, or `zonotope([])` (the empty set) if `try` failed. -/
def NonlinearARX.reachStepCora : Option (Set α) → Set α
  | some Y => Y
  | none => ∅

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
