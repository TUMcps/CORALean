module

public import CORALean.ContSet.Zonotope.Real.Operations.ReduceMat
public import CORALean.ContSet.Zonotope.Real.Theorems.Basic
public import CORALean.ContSet.Zonotope.Real.Theorems.ReduceGirardOuter

@[expose] public section

/-!
# The reduction of a matrix zonotope over-approximates

The stacked zonotope denotes the stackings of the members (`vec_toSet`), Girard's reduction
encloses it (`reduceGirard_outer`), and the image under the unstacking (`map_exact`) of an
enclosure of the stackings encloses the matrices.

## Inputs
* `Z` – matrix zonotope
* `o` – target order

## Hypotheses
* none

## Conclusion
* `Z` lies in its reduction
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.reduceMat_outer (Z : Zonotope (Mat ℝ m n)) (o : ℕ) : -- --- CONCL ---
    Z.toSet ⊆ (Z.reduceMat o).toSet := by -- --- PROOF ---
  -- the members are the unstackings of the members of the stacked zonotope
  have hZ : Z.toSet = matVecEquiv.symm '' Z.vec.toSet := by
    rw [← Zonotope.vec_toSet, Set.image_image]
    simp
  -- which the reduction of the stacked zonotope encloses, and the unstacking maps exactly
  rw [hZ, Zonotope.reduceMat, ← Zonotope.map_exact]
  exact Set.image_mono (Zonotope.reduceGirard_outer Z.vec o)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
