module

public import CORALean.ContDynamics.LinearSysDT.Definitions.ReachInner
public import CORALean.ContDynamics.LinearSysDT.Theorems.ReachSetExactInnerOfOuter
public import CORALean.ContDynamics.LinearSysDT.Theorems.Real.ReachSubsetReachSetExactAddError
public import CORALean.ContSet.Zonotope.Real.Theorems.CenterMemConstruct
public import CORALean.ContSet.Zonotope.Real.Theorems.IsBounded
public import CORALean.ContSet.Zonotope.Real.Theorems.IsCompact

@[expose] public section

/-!
# The first inner approximation of a reachable set in this development

`reachSetExact` on the *right* of the inclusion, which no other reachability theorem here does:
`reach_outer` and `reachSetExact_outer` both say the computed set is the larger one, and this says
a computed set is the smaller one. Nothing is left to discharge at the call site.
`reach_subset_reachSetExact_add_error` supplies the enclosure `reachSetExact_inner_of_outer` asks
for, and every hypothesis that bridge places on the sets is a zonotope fact already in the tree —
`convex_construct` and `isCompact_construct` for `R₀` and `U`, and `center_mem_construct` with
`isBounded_construct` for the error. So the run's own accumulated error is exactly what has to
come off it, and nothing about the system beyond linearity enters.

## Inputs
* `sys` – system
* `o` – maximum zonotope order
* `R₀` – initial zonotope
* `U` – input zonotope
* `k` – step

## Hypotheses
* `ho` – order positive

## Conclusion
* the inner approximation lies in the exact reachable set
-/

-- Authors:       Claude Sonnet 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The computed run minus its own accumulated error is *contained in* the
exact reachable set. -/
theorem LinearSysDT.reachInner_inner (sys : LinearSysDT ℝ n) {o : ℕ} (ho : 0 < o)
    (R₀ U : Zonotope (Vec ℝ n)) (k : ℕ) :
    sys.reachInner o ho R₀ U k ⊆ sys.reachSetExact (S := 𝒵) R₀ U k :=
  sys.reachSetExact_inner_of_outer (S := 𝒵) (Zonotope.convex_construct R₀)
    (Zonotope.isCompact_construct R₀) (Zonotope.convex_construct U)
    (Zonotope.isCompact_construct U) k ⟨_, Zonotope.center_mem_construct _⟩
    (Zonotope.isBounded_construct _) (sys.reach_subset_reachSetExact_add_error ho R₀ U k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
