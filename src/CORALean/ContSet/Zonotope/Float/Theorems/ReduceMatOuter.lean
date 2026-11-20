module

public import CORALean.ContSet.Zonotope.Float.Operations.ReduceMat
public import CORALean.ContSet.Zonotope.Float.Theorems.ReduceGirardOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.UnvecExact

@[expose] public section

/-!
# The reduction of a matrix zonotope over-approximates, over a floating-point scalar

The stacked zonotope denotes the stackings of the members (`vec_exact`), Girard's reduction
encloses it (`reduceGirard_outer`), and unstacking is exact (`unvec_exact`): the unstacking of an
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

namespace CORALean.Float

open InflatedContSet FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.reduceMat_outer (Z : Zonotope (Mat 𝕋 m n)) (o : ℕ) : -- --- CONCL ---
    Z.toSet ⊆ (Z.reduceMat o).toSet := by -- --- PROOF ---
  -- the members are the unstackings of the members of the stacked zonotope
  have hZ : Z.toSet = matVecEquiv.symm '' Z.vec.toSet := by
    rw [Zonotope.vec_exact, Set.image_image]
    simp
  -- which the reduction of the stacked zonotope encloses, and unstacking is exact
  rw [hZ, Zonotope.reduceMat, Zonotope.unvec_exact]
  exact Set.image_mono (Zonotope.reduceGirard_outer Z.vec o)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
