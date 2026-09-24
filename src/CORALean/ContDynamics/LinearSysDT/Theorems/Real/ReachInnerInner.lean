import CORALean.ContDynamics.LinearSysDT.Definitions.ReachInner
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachSetInnerOfOuter
import CORALean.ContDynamics.LinearSysDT.Theorems.Real.ReachSubsetReachSetAddError
import CORALean.ContSet.Zonotope.Real.Theorems.CentreMemConstruct
import CORALean.ContSet.Zonotope.Real.Theorems.IsBounded
import CORALean.ContSet.Zonotope.Real.Theorems.IsCompact

/-!
# The first inner approximation of a reachable set in this development

`reachSet` on the *right* of the inclusion, which no other reachability
theorem here does: `reach_outer` and `reachSet_outer` both say the computed set
is the larger one, and this says a computed set is the smaller one.

Nothing is left to discharge at the call site. `reach_subset_reachSet_add_error`
supplies the enclosure `reachSet_inner_of_outer` asks for, and every hypothesis
that bridge places on the sets is a zonotope fact already in the tree —
`convex_construct` and `isCompact_construct` for `R₀` and `U`, and
`centre_mem_construct` with `isBounded_construct` for the error.

So the run's own accumulated error is exactly what has to come off it, and
nothing about the system beyond linearity enters.
-/

-- Authors:       Tobias Ladner
-- Written:       08-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The computed run minus its own accumulated error is *contained in* the
exact reachable set. -/
theorem LinearSysDT.reachInner_inner (sys : LinearSysDT ℝ n) {o : ℕ} (ho : 0 < o)
    (R₀ U : Zonotope (Vec ℝ n)) (k : ℕ) :
    sys.reachInner o ho R₀ U k ⊆ sys.reachSet (S := 𝒵) R₀ U k :=
  sys.reachSet_inner_of_outer (S := 𝒵) (Zonotope.convex_construct R₀)
    (Zonotope.isCompact_construct R₀) (Zonotope.convex_construct U)
    (Zonotope.isCompact_construct U) k ⟨_, Zonotope.centre_mem_construct _⟩
    (Zonotope.isBounded_construct _) (sys.reach_subset_reachSet_add_error ho R₀ U k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
