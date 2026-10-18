module

public import CORALean.HybridDynamics.Theorems.ReachFloatOuter
public import CORALean.HybridDynamics.Theorems.ReachSetExactEqIUnionIsRunUntil

@[expose] public section

/-!
# `HybridAutomaton.reachFloat` encloses the reachable set up to its horizon

`reachFloat_outer` at the level of `reachSetExact`: of the slices
`reachSetExact_eq_iUnion_isRunUntil` cuts the reachable set into, every one with a
duration bound `T ≤ tFinal` and at most `K` jumps lies in the computed sets of
the location `ℓ`. Runs longer than the horizon, or with more jumps, are not
claimed, as CORA's `reach` claims none past `tFinal`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float ContSet

variable {n : ℕ} {L 𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The part of `reachSetExact X₀ ℓ₀ ℓ` reached within `tFinal` and `K` jumps lies in the
sets `reachFloat` computed for `ℓ`. -/
theorem HybridAutomaton.reachSetExact_subset_reachFloat
    (HA : HybridAutomaton 𝒵[𝕋] (fun k => HPolytope 𝕋 (Vec 𝕋 k)) L 𝕋
    n) {tFinal : ℚ} {options : LinearSys.ReachOptions 𝕋} {K : ℕ} {ℓ₀ : L} {X₀ : Zonotope (Vec 𝕋 n)}
    (ℓ : L) : -- --- STMT ---
    ∀ out ∈ HA.reachFloat tFinal options K ℓ₀ X₀,
      (⋃ (T : ℝ) (_ : T ≤ tFinal) (k : ℕ) (_ : k ≤ K),
          {y | ∃ x ∈ construct X₀, HA.IsRunUntil T k ℓ₀ x ℓ y})
        ⊆ {y | ∃ p ∈ out, p.1 = ℓ ∧ y ∈ construct p.2} := by -- --- PROOF ---
  intro out (h : HA.reachFloat tFinal options K ℓ₀ X₀ = some out) y hy
  simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hy
  obtain ⟨T, hT, k, hk, x, hx, run⟩ := hy
  exact HA.reachFloat_outer run hT hk hx _ h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
