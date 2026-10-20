module

public import CORALean.ContSet.ContSet.ContSet
public import CORALean.Specification.Specification

@[expose] public section

/-!
# `NonlinearARX.reachStepCora`, the output set CORA's `reach` stores for one step

CORA's `@nonlinearARX/reach.m` [1], linearize-and-reformulate branch (`otherwise`), step `k`: the
body from `linReach` (l. 139) to the output set `Y_d` (l. 147-152) sits in `try` (l. 137), and
`catch` (l. 154-155) sets `Y_d = zonotope([])`. `zonotope([])` has empty center and generators,
which `isemptyobject` reads as the empty set. Either way l. 158 stores `Y_d` as
`timePoint.set{k}` and l. 164-166 hand it to `check`: the error is neither rethrown nor warned
about.

The computation inside `try` is abstracted to `attempt`: `some Y` when it succeeds, `none` when
any statement in it errors. Sets are `Set α`, the empty zonotope being `∅`.

# CORA's `nonlinearARX/reach` passes any specification on a step that errored

If the `try` body of a step fails, `Y_d = zonotope([])` is the empty set, so `check` finds a safe
set or invariant containing it (`contains` of an empty inner set is `true`, `@contSet/contains.m`
l. 105) and an unsafe set disjoint from it, whatever the system does. The failing computation is
abstracted as an arbitrary error: `Ytrue`, the set the step ought to have produced, may violate
the specification, and the verdict is `true` all the same.

## Inputs
* `spec` – specification
* `Ytrue` – true output set

## Hypotheses
* `_hviolated` – the specification fails on the true set

## Conclusion
* CORA's stored output set after an error satisfies the specification

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


-- The model: CORA's code as printed, kept only to be refuted.
/-- `timePoint.set{k}`: the computed `Y_d`, or `zonotope([])` (the empty set) if `try` failed. -/
def NonlinearARX.reachStepCora : Option (Set α) → Set α
  | some Y => Y
  | none => ∅

end CORALean

namespace CORALean

variable {C α : Type} [CORALean.ContSet C α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinearARX.reachStepCora_holds_of_error (spec : Specification C) (Ytrue : Set α)
    (_hviolated : ¬ spec.Holds Ytrue) :
    spec.Holds (NonlinearARX.reachStepCora (none : Option (Set α))) := by
  unfold Specification.Holds NonlinearARX.reachStepCora
  cases spec.kind <;> simp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
