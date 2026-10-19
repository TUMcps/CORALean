module

public import CORALean.HybridDynamics.Definitions.GuardIntersectZonoGirard
public import CORALean.HybridDynamics.Counterexamples.RobustProjectionCora

@[expose] public section

/-!
# `Location.guardIntersectZonoGirardCora`: the guard enclosure with CORA's pinning

`Location.guardIntersectZonoGirard` with the step it leaves out: after the cuts of each basis `D`
are joined into `lb`, `ub`, they pass through `aux_robustProjection`
(`Location.robustProjectionCora`) before the box is formed, as CORA's `aux_enclosingInterval`
does. Everything else is as there (no `aux_tightenSet`, the dual bound for the cut).

# `Location.guardIntersectZonoGirardCora` misses every state of the hyperplane

With the guard `2 x₁ = 4` (normal `(2, 0)`, `γ = 4`) and the standard basis, which CORA's
`'box'` option computes (`calcBasis`), the pinning of `aux_robustProjection` puts the first
coordinate of CORA's box at `8`, so the enclosure holds no state of the hyperplane `x₁ = 2`,
whatever the reach sets: a reach state with `x₁ = 2` is cut away. Neither `guardIntersect` nor
the `polytope` constructor normalises the guard.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n : ℕ}


-- The model: CORA's code as printed, kept only to be refuted.
/-- The enclosure of the reach sets `R₀ :: Rs` with `{x | x·nv = γ}` by the bases `Bs`, with the
pinning of `aux_robustProjection`. -/
noncomputable def Location.guardIntersectZonoGirardCora (Bs : List (Mat ℝ n n))
    (R₀ : Real.Zonotope (Vec ℝ n)) (Rs : List (Real.Zonotope (Vec ℝ n))) (nv : Vec ℝ n)
    (γ : ℝ) : Set (Vec ℝ n) :=
  let upper : Real.Zonotope (Vec ℝ n) → Vec ℝ n → ℝ := fun Z ℓ => Location.zonoGirardUpper Z nv γ ℓ
  let lower : Real.Zonotope (Vec ℝ n) → Vec ℝ n → ℝ := fun Z ℓ => -upper Z (-ℓ)
  let lb : Vec ℝ n → ℝ := fun ℓ => Rs.foldl (fun m Z => min m (lower Z ℓ)) (lower R₀ ℓ)
  let ub : Vec ℝ n → ℝ := fun ℓ => Rs.foldl (fun m Z => max m (upper Z ℓ)) (upper R₀ ℓ)
  ⋂ i : Fin Bs.length,
    -- `[lb, ub] = aux_robustProjection(B, n, gamma, lb, ub)`
    let lu := Location.robustProjectionCora Bs[i] nv γ (fun k => lb (Bs[i]ᵀ k))
      (fun k => ub (Bs[i]ᵀ k))
    (fun y => Bs[i] *ᵥ y) '' {y | ∀ k, lu.1 k ≤ y k ∧ y k ≤ lu.2 k}

end CORALean

namespace CORALean

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- No state on the hyperplane `x₁ = 2` lies in the enclosure, for any reach sets. -/
theorem Location.guardIntersectZonoGirardCora_counterexample
    (R₀ : Real.Zonotope (Vec ℝ 2)) (Rs : List (Real.Zonotope (Vec ℝ 2))) : -- --- CONCL ---
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
