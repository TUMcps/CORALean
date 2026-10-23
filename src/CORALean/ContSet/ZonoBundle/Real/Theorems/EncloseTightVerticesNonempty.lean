module

public import CORALean.ContSet.ZonoBundle.Real.Operations.EncloseTightVertices
public import CORALean.ContSet.Conversion.Real.Theorems.Basic

@[expose] public section

/-!
# The joined vertices of two nonempty bundles span a nonempty set

The vertex polytope `encloseTightVertices` denotes the convex hull of the two bundles' union
(`VPolytope.convHull_exact`), which holds a point of the first.

## Inputs
* `zB₁` – first bundle
* `zB₂` – second bundle

## Hypotheses
* `hk₁` – first bundle has a member
* `hk₂` – second bundle has a member
* `hne₁` – first bundle nonempty
* `hne₂` – second bundle nonempty

## Conclusion
* the joined vertices denote a nonempty set
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.encloseTightVertices_nonempty (zB₁ zB₂ : ZonoBundle (Vec ℝ n))
    (hk₁ : 0 < zB₁.k) (hk₂ : 0 < zB₂.k) (hne₁ : zB₁.construct.Nonempty)
    (hne₂ : zB₂.construct.Nonempty) :
    (zB₁.encloseTightVertices zB₂ hk₁ hk₂ hne₁ hne₂).construct.Nonempty := by
  unfold ZonoBundle.encloseTightVertices
  rw [VPolytope.convHull_exact]
  obtain ⟨x, hx⟩ := hne₁
  exact ⟨x, subset_convexHull ℝ _ (Or.inl (by rw [ZonoBundle.vPolytopeAll_exact]; exact hx))⟩


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
