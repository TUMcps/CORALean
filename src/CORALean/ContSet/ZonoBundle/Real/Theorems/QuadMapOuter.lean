module

public import CORALean.ContSet.ZonoBundle.Real.Operations.QuadMap
public import CORALean.ContSet.Zonotope.Real.Theorems.BilinOuter

@[expose] public section

/-!
# `ZonoBundle.quadMap` is an outer approximation

A point of the bundle lies in every member, so its image `x ↦ (xᵀ Q_k x)_k` lies in the zonotope
quadratic map of every member (`Zonotope.bilin_outer` at `(x, x)`). Outer only: the bilinear map of
a zonotope with itself is an enclosure (the cross coefficients are free), and the intersection
makes the image of the bundle smaller still.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Outer: the quadratic image of the bundle is inside the bundle `quadMap` returns. -/
theorem ZonoBundle.quadMap_outer (Q : Fin m → Mat ℝ n n) (zB : ZonoBundle (Vec ℝ n)) :
    (fun x => PolyZonotope.quadBilin Q x x) '' zB.construct ⊆
      (zB.quadMap Q).construct := by -- --- PROOF ---
  rintro _ ⟨a, ha, rfl⟩
  simp only [ZonoBundle.construct, Set.mem_iInter] at ha ⊢
  intro i
  exact Zonotope.bilin_outer (PolyZonotope.quadBilin Q) (zB.Z i) (zB.Z i)
    (Set.mem_biUnion (ha i) ⟨a, ha i, rfl⟩)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
