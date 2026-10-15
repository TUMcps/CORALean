module

public import CORALean.ContSet.PolyZonotope.Real.PolyZonotope

@[expose] public section

/-!
# CORA's corner images

`V(:,i)` of `aux_polyVertices` in `isPolytope` [1]: the image of a cube corner.

## References

* [1] `contSet/@polyZonotope/isPolytope.m`, CORA (Sep. 2025), by N. Kochdumper (2019).
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The images of the cube corners, `V(:,i)` of `aux_polyVertices`: `c + Σⱼ G(:,j) ∏ I^E(:,j)`. -/
def PolyZonotope.coraVertex (pZ : PolyZonotope α) (I : Fin pZ.p → ℝ) : α :=
  pZ.c + ∑ j, PolyZonotope.monomial pZ.E I j • pZ.G j

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
