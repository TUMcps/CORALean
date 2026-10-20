module

public import CORALean.ContDynamics.LinearSysDT.Definitions.ReachInnerFloat
public import CORALean.ContDynamics.LinearSysDT.Theorems.ReachFloatSubsetReachSetExactAddError
public import CORALean.ContDynamics.LinearSysDT.Theorems.ReachSetExactInnerOfOuter
public import CORALean.ContSet.Zonotope.Real.Theorems.CenterMemConstruct
public import CORALean.ContSet.Zonotope.Real.Theorems.IsBounded
public import CORALean.ContSet.Zonotope.Real.Theorems.IsCompact

@[expose] public section

/-!
# The float inner approximation of a reachable set

`reachInner_inner` at the float layer: `reachInnerFloat` puts the computed float run's own error
back off the run, and the result lands *inside* `reachSetExact` — the exact, real-valued reachable
set read from the nominal parts of `R₀` and `U` — the same reversed direction `reachInner_inner`
states, now for a run computed in a machine scalar. The bridge is `reachSetExact_inner_of_outer`
again: `reach_float_subset_reachSetExact_add_error` supplies the enclosure, and every further
hypothesis is a fact about the nominal zonotopes, already in the tree at `Real`. New relative to
`Real` are `hR₀`, `hU`: a float run's own error box has no guaranteed shape, so they are asked of
the caller.

## Inputs
* `sys` – system
* `o` – maximum zonotope order
* `R₀` – initial float zonotope
* `U` – input float zonotope
* `k` – step

## Hypotheses
* `ho` – order positive
* `hR₀` – initial error box contains the origin
* `hU` – input error box contains the origin

## Conclusion
* the float inner approximation lies in the exact reachable set
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float
open CORALean.Float.InflatedContSet
open scoped CORALean.Real

variable {n : ℕ} {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The float run minus its own accumulated error is *contained in* the exact
reachable set, read from the nominal parts of `R₀` and `U` — the float
counterpart of `reachInner_inner`. -/
theorem LinearSysDT.reachInnerFloat_inner (sys : LinearSysDT 𝕋 n) {o : ℕ} (ho : 0 < o)
    {R₀ U : Zonotope (Vec 𝕋 n)} (hR₀ : (0 : Vec ℝ n) ∈ R₀.I_error.construct)
    (hU : (0 : Vec ℝ n) ∈ U.I_error.construct) (k : ℕ) :
    sys.reachInnerFloat o ho R₀ U k ⊆
      sys.reachSetExact (S := 𝒵)
        (nominal R₀) (nominal U) k :=
  sys.reachSetExact_inner_of_outer (S := 𝒵)
    (Real.Zonotope.convex_construct _) (Real.Zonotope.isCompact_construct _)
    (Real.Zonotope.convex_construct _) (Real.Zonotope.isCompact_construct _) k
    ⟨_, Real.Zonotope.center_mem_construct _⟩ (Real.Zonotope.isBounded_construct _)
    (sys.reach_float_subset_reachSetExact_add_error ho hR₀ hU k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
