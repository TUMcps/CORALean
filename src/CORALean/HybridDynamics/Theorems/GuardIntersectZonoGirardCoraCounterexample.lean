import CORALean.HybridDynamics.Definitions.GuardIntersectZonoGirardCora
import CORALean.HybridDynamics.Theorems.RobustProjectionCoraCounterexample

/-!
# `Location.guardIntersectZonoGirardCora` misses every state of the hyperplane

With the guard `2 x₁ = 4` (normal `(2, 0)`, `γ = 4`) and the standard basis, which CORA's
`'box'` option computes (`calcBasis`), the pinning of `aux_robustProjection` puts the first
coordinate of CORA's box at `8`, so the enclosure holds no state of the hyperplane `x₁ = 2`,
whatever the reach sets: a reach state with `x₁ = 2` is cut away. Neither `guardIntersect` nor
the `polytope` constructor normalises the guard.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- No state on the hyperplane `x₁ = 2` lies in the enclosure, for any reach sets. -/
theorem Location.guardIntersectZonoGirardCora_counterexample
    (R₀ : Real.Zonotope (Vec ℝ 2)) (Rs : List (Real.Zonotope (Vec ℝ 2))) :
    ∀ x : Vec ℝ 2, x ⬝ᵥ ![2, 0] = 4 →
      x ∉ Location.guardIntersectZonoGirardCora [(1 : Mat ℝ 2 2)] R₀ Rs ![2, 0]
        4 := by -- --- PROOF ---
  intro x hx hmem
  -- the single basis `1` carries the box to itself
  have h := Set.mem_iInter.mp hmem ⟨0, by simp⟩
  obtain ⟨y, hy, rfl⟩ := h
  change (1 : Mat ℝ 2 2) *ᵥ y ⬝ᵥ ![2, 0] = 4 at hx
  rw [one_mulVec] at hx
  exact Location.robustProjectionCora_counterexample _ _ y hx hy

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
