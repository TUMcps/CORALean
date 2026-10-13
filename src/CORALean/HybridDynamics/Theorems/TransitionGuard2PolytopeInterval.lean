module

public import CORALean.HybridDynamics.Theorems.TransitionGuard2PolytopeExact
public import CORALean.ContSet.Conversion.Real.Interval_to_HPolytope
public import CORALean.ContSet.HPolytope.Real.Instances
public import CORALean.ContSet.Interval.Real.Instances

@[expose] public section

/-!
# `Transition.guard2polytope` of a box guard

A box guard, converted by `Interval.hPolytope`, is the same guard: exact
(`Interval.hPolytope_exact`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {L : Type} {𝕋 : Type} {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A box guard, converted by `Interval.hPolytope`, is the same guard: exact. -/
theorem Transition.guard2polytope_interval
    (e : Transition (fun n => Real.Interval (Vec ℝ n)) L 𝕋 n) :
    construct (e.guard2polytope (P := fun n => Real.HPolytope (Vec ℝ n))
      Real.Interval.hPolytope).guard = construct e.guard :=
  Transition.guard2polytope_exact _ (fun g => Real.Interval.hPolytope_exact g) e

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
