module

public import CORALean.ContSet.Zonotope.Float.Operations.Abs
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Zonotope.Real.Theorems.AbsCornerMem
public import CORALean.ContSet.Zonotope.Float.Theorems.AbsNominal

@[expose] public section

/-!
# The corner of `abs` is a point of its nominal part

The corner `|c| + Σ |gⱼ|` of the stored floats is a point of the nominal part of `abs Z`, as at
the real layer.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The corner `|c| + Σ |gⱼ|` of the stored floats is a point of the nominal part of `abs Z`. -/
theorem Zonotope.abs_corner_mem_nominalSet (Z : Zonotope (Vec 𝕋 n)) :
    (fun i => (nominal Z).absBound i) ∈ nominalSet Z.abs := by
  have := CORALean.Real.Zonotope.abs_corner_mem (nominal Z)
  rw [← Zonotope.abs_nominal] at this
  exact this

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
