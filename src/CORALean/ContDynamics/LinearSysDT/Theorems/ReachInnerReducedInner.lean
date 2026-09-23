import CORALean.ContDynamics.LinearSysDT.Definitions.ReachInnerReduced
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachSetInnerOfOuter
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachSubsetReachSetAddErrorReduced
import CORALean.ContSet.Zonotope.Real.Theorems.CentreMemConstruct
import CORALean.ContSet.Zonotope.Real.Theorems.IsBounded
import CORALean.ContSet.Zonotope.Real.Theorems.IsCompact

/-!
# The inner approximation at the reduced error

`reachInner_inner` with `reachErrorReduced` in place of `reachError`, and the
same bridge doing the work: `reach_subset_reachSet_add_errorReduced` supplies
the enclosure `reachSet_inner_of_outer` asks for, and the reduced error is a
zonotope, so nonempty and bounded come from the representation exactly as
before.

Weaker than `reachInner_inner` in what it delivers, not in what it claims —
`reachInnerReduced_subset_reachInner` measures the gap — and the reason to want
it is `reachErrorReduced_h_le`: this subtrahend's description stays at `o * n`,
so a caller gets an inner approximation whose cost does not grow with the
horizon.
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

/-- The computed run minus its reduced error is *contained in* the exact
reachable set — the same guarantee as `reachInner_inner`, on a smaller set,
bought with a bounded generator count. -/
theorem LinearSysDT.reachInnerReduced_inner (sys : LinearSysDT ℝ n) {o : ℕ} (ho : 0 < o)
    (R₀ U : Zonotope (Vec ℝ n)) (k : ℕ) :
    sys.reachInnerReduced o ho R₀ U k ⊆ sys.reachSet (S := 𝒵) R₀ U k :=
  sys.reachSet_inner_of_outer (S := 𝒵) (Zonotope.convex_construct R₀)
    (Zonotope.isCompact_construct R₀) (Zonotope.convex_construct U)
    (Zonotope.isCompact_construct U) k ⟨_, Zonotope.centre_mem_construct _⟩
    (Zonotope.isBounded_construct _) (sys.reach_subset_reachSet_add_errorReduced ho R₀ U k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
