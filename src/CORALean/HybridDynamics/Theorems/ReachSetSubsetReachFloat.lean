import CORALean.HybridDynamics.Theorems.ReachFloatOuter
import CORALean.HybridDynamics.Theorems.ReachSetEqIUnionRunUntil

/-!
# `HybridAutomaton.reachFloat` encloses the reachable set up to its horizon

`reachFloat_outer` at the level of `reachSet`: of the slices
`reachSet_eq_iUnion_runUntil` cuts the reachable set into, every one with a
duration bound `T ≤ tFinal` and at most `K` jumps lies in the computed sets of
the location `ℓ`. Runs longer than the horizon, or with more jumps, are not
claimed, as CORA's `reach` claims none past `tFinal`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float ContSet

variable {n : ℕ} {L 𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The part of `reachSet X₀ ℓ₀ ℓ` reached within `tFinal` and `K` jumps lies in the
sets `reachFloat` computed for `ℓ`. -/
theorem HybridAutomaton.reachSet_subset_reachFloat
    (HA : HybridAutomaton (fun k => Zonotope (Vec 𝕋 k)) (fun k => HPolytope 𝕋 (Vec 𝕋 k)) L 𝕋
    n) {tFinal : ℚ}
    {options : LinearSys.ReachOptions 𝕋} {K : ℕ} {ℓ₀ : L} {X₀ : Zonotope (Vec 𝕋 n)}
    {out : List (L × Zonotope (Vec 𝕋 n))} (h : HA.reachFloat tFinal options K ℓ₀ X₀ = some out)
    (ℓ : L) :
    (⋃ (T : ℝ) (_ : T ≤ tFinal) (k : ℕ) (_ : k ≤ K),
        {y | ∃ x ∈ construct X₀, HA.RunUntil T k ℓ₀ x ℓ y})
      ⊆ {y | ∃ p ∈ out, p.1 = ℓ ∧ y ∈ construct p.2} := by
  intro y hy
  simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hy
  obtain ⟨T, hT, k, hk, x, hx, run⟩ := hy
  exact HA.reachFloat_outer run hT hk hx h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
