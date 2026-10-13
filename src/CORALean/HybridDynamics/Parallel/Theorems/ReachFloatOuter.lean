import CORALean.HybridDynamics.Parallel.Operations.ReachFloat
import CORALean.HybridDynamics.Parallel.Theorems.RunToProduct
import CORALean.HybridDynamics.Theorems.ReachFloatOuter
import CORALean.HybridDynamics.Theorems.RunIffExistsRunUntil

/-!
# The float run of the product encloses every run of the parallel automaton

A run of the parallel automaton from initial states in `X₀` (stacked) is a run of the product
(`Run.toProduct`), so it has a duration and a jump count there (`run_iff_exists_runUntil`), and
when those fit the horizon `tFinal` and the bound `K`, its stacked end state lies in a set
`ParallelHybridAutomaton.reachFloat` computed for its final location tuple. An outer statement.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float ContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]
variable {k m : ℕ} {n : Fin k → ℕ} {L : Fin k → Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ParallelHybridAutomaton.reachFloat_outer
    {P : ParallelHybridAutomaton (fun k => Zonotope (Vec 𝕋 k)) (fun k => HPolytope 𝕋 (Vec 𝕋 k)) k L
    𝕋 n m} (hself : P.SelfBindFree)
    (lift : ParallelHybridAutomaton.Lifting (fun k => Zonotope (Vec 𝕋 k))
    (fun k => HPolytope 𝕋 (Vec 𝕋 k)) n m P.binds)
    {tFinal : ℚ} {options : LinearSys.ReachOptions 𝕋} {K : ℕ} {ℓ₀ ℓ : ∀ i, L i}
    {X₀ : Zonotope (Vec 𝕋 (∑ i, n i))} {out : List ((∀ i, L i) × Zonotope (Vec 𝕋 (∑ i, n i)))}
    (h : P.reachFloat lift tFinal options K ℓ₀ X₀ = some out)
    {x y : ∀ i, Vec ℝ (n i)} (hx : stack x ∈ construct X₀) (run : P.Run ℓ₀ x ℓ y) :
    ∃ (T : ℝ) (j : ℕ), (P.product lift).RunUntil T j ℓ₀ (stack x) ℓ (stack y) ∧
      (T ≤ tFinal → j ≤ K → ∃ p ∈ out, p.1 = ℓ ∧ stack y ∈ construct p.2) := by
  -- the parallel run is a run of the product, which has a duration and a jump count
  obtain ⟨T, j, hrun⟩ := HybridAutomaton.run_iff_exists_runUntil.mp (run.toProduct hself lift)
  exact ⟨T, j, hrun, fun hT hj => (P.product lift).reachFloat_outer hrun hT hj hx h⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
