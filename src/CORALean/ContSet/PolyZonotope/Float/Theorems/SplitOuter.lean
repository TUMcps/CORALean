module

public import CORALean.ContSet.PolyZonotope.Float.Operations.Split
public import CORALean.ContSet.Zonotope.Float.Theorems.ReduceMethCOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.SplitOuter
public import CORALean.ContSet.Conversion.Float.Operations.PolyZonotope_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Theorems.ConPolyZonoPolyZonotopeContains
public import CORALean.ContSet.Conversion.Float.Theorems.Basic
public import CORALean.ContSet.Conversion.Float.Theorems.PolyZonotopeZonotopeContains
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopePolyZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.PolyZonotopeZonotopeContains

@[expose] public section

/-!
# The halves of `split` cover the polynomial zonotope, over a floating-point scalar

The parallelotope encloses the zonotope of `pZ` (`reduceMethC_outer`), which encloses `pZ`
(`zonotope_contains`); its two halves cover it (`Zonotope.split_outer`), and each half's
polynomial zonotope contains it (`polyZonotope_contains`). Outer, not exact: the union of the
halves contains `pZ` along any generator, and is in general larger.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.split_outer (pZ : PolyZonotope (Vec 𝕋 n))
    (j : Fin pZ.splitParallelotope.h) :
    pZ.construct ⊆ (pZ.split j).fst.construct ∪ (pZ.split j).snd.construct := by -- --- PROOF ---
  intro x hx
  -- the parallelotope holds the zonotope, which holds the set
  have hP : x ∈ pZ.splitParallelotope.construct :=
    Zonotope.reduceMethC_outer pZ.zonotope 1 (pZ.zonotope_contains hx)
  rcases Zonotope.split_outer _ j hP with h | h
  · exact Or.inl ((pZ.splitParallelotope.split j).fst.polyZonotope_contains h)
  · exact Or.inr ((pZ.splitParallelotope.split j).snd.polyZonotope_contains h)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
