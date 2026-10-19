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

`reachInner_inner` at the float layer: `reachInnerFloat` puts the computed
float run's own error back off the run, and the result lands *inside*
`reachSetExact` — the exact, real-valued reachable set read from the nominal parts
of `R₀` and `U` — which is the same reversed direction `reachInner_inner`
states, now for a run computed in a machine scalar.

The bridge is `reachSetExact_inner_of_outer` again, discharged the same way:
`reach_float_subset_reachSetExact_add_error` supplies the enclosure, and every
further hypothesis is a fact about the *nominal* zonotopes `R₀` and `U`
denote, already in the tree at `Real`. `reachErrorFloat k` is a real zonotope,
so nonempty and bounded come from `center_mem_construct` and
`isBounded_construct` exactly as at `reachInner_inner`.

What is new relative to `Real` is `hR₀`, `hU`: a float run's own error box has
no guaranteed shape, so the two hypotheses `reach_float_subset_reachSetExact_add_error`
needs are asked of the caller here rather than derived.
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
    (hU : (0 : Vec ℝ n) ∈ U.I_error.construct) (k : ℕ) : -- --- STMT ---
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
