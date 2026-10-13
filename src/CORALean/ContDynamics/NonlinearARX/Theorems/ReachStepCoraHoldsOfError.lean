module

public import CORALean.ContDynamics.NonlinearARX.Operations.ReachStepCora
public import CORALean.Specification.Specification

@[expose] public section

/-!
# CORA's `nonlinearARX/reach` passes any specification on a step that errored

If the `try` body of a step fails, `Y_d = zonotope([])` is the empty set, so `check` finds a safe
set or invariant containing it (`contains` of an empty inner set is `true`, `@contSet/contains.m`
l. 105) and an unsafe set disjoint from it, whatever the system does. The failing computation is
abstracted as an arbitrary error: `Ytrue`, the set the step ought to have produced, may violate
the specification, and the verdict is `true` all the same.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

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
