module

public import CORALean.HybridDynamics.Parallel.Operations.ReachFloat
public import CORALean.HybridDynamics.Parallel.Theorems.IsRunToProductWith
public import CORALean.HybridDynamics.Parallel.Theorems.MergeFlowsFlowLaw
public import CORALean.HybridDynamics.Theorems.ReachFloatOuter
public import CORALean.HybridDynamics.Theorems.IsRunIffExistsIsRunUntil

@[expose] public section

/-!
# The float run of the product encloses every run of the parallel automaton

A run of the parallel automaton from initial states in `X₀` (stacked) is a run of the product at
`mergeFlows` (`IsRun.toProductWith`, by `mergeFlows_flowLaw` at state-bound components without
self-binding), so it has a duration and a jump count there (`isRun_iff_exists_isRunUntil`), and when
those fit the horizon `tFinal` and the bound `K`, its stacked end state lies in a set
`ParallelHybridAutomaton.reachFloat` computed for its final location tuple. An outer statement.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float ContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]
variable {k m : ℕ} {n : Fin k → ℕ} {L : Fin k → Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ParallelHybridAutomaton.reachFloat_outer
    {P : ParallelHybridAutomaton 𝒵[𝕋] (fun k => HPolytope 𝕋 (Vec 𝕋 k)) k L 𝕋 n m}
    (hst : P.StateBound) (hself : P.SelfBindFree)
    (lift : ParallelHybridAutomaton.Lifting 𝒵[𝕋] (fun k => HPolytope 𝕋 (Vec 𝕋 k)) n m) {tFinal : ℚ}
    {options : LinearSys.ReachOptions 𝕋} {K : ℕ} {ℓ₀ ℓ : ∀ i, L i}
    {X₀ : Zonotope (Vec 𝕋 (∑ i, n i))} {x y : ∀ i, Vec ℝ (n i)} (hx : stack x ∈ construct X₀)
    (run : P.IsRun ℓ₀ x ℓ y) : -- --- STMT ---
    ∀ out ∈ P.reachFloat lift tFinal options K ℓ₀ X₀,
      ∃ (T : ℝ) (j : ℕ), (P.productWith lift P.mergeFlows (P.mergeInputSets lift)
        (P.mergeDistSets lift)).IsRunUntil T j ℓ₀ (stack x) ℓ (stack y) ∧
        (T ≤ tFinal → j ≤ K → ∃ p ∈ out, p.1 = ℓ ∧ stack y ∈ construct p.2) := by -- --- PROOF ---
  intro out (h : P.reachFloat lift tFinal options K ℓ₀ X₀ = some out)
  -- the parallel run is a run of the product, which has a duration and a jump count
  obtain ⟨T, j, hrun⟩ := HybridAutomaton.isRun_iff_exists_isRunUntil.mp
    (run.toProductWith (P.mergeFlows_flowLaw hst hself lift) lift)
  exact ⟨T, j, hrun, fun hT hj => HybridAutomaton.reachFloat_outer _ hrun hT hj hx _ h⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
