module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Split
public import CORALean.ContSet.Zonotope.Real.Theorems.ReduceMethCOuter
public import CORALean.ContSet.Zonotope.Real.Theorems.SplitUnion

@[expose] public section

/-!
# The halves of `split` cover the polynomial zonotope

The parallelotope encloses `zonotope(pZ)` (`reduceMethC_outer`), which encloses `pZ`
(`zonotope_contains`); its two halves cover it exactly (`Zonotope.split_union`), and the
polynomial zonotope of a zonotope denotes it (`Zonotope.polyZonotope_exact`). So the union of
the two halves, along any generator, is an over-approximation of `pZ`, not equal to it.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.split_outer (pZ : PolyZonotope (Vec ℝ n))
    (j : Fin pZ.splitParallelotope.h) :
    pZ.construct ⊆ (pZ.split j).fst.construct ∪ (pZ.split j).snd.construct := by
  unfold PolyZonotope.split
  rw [← Zonotope.polyZonotope_exact, ← Zonotope.polyZonotope_exact,
    Zonotope.split_union pZ.splitParallelotope j]
  exact (pZ.zonotope_contains).trans (Zonotope.reduceMethC_outer _ 1)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
