module

public import CORALean.ContSet.Zonotope.Float.Operations.Reduce
public import CORALean.ContSet.Zonotope.Float.Theorems.ReduceGirardOuter

@[expose] public section

/-!
# `Zonotope.reduce` over-approximates the zonotope

Girard's is the rule `reduce` runs, and this is the whole of that choice: any
other rule would discharge it too.
-/

-- Authors:       Claude Opus 5
-- Written:       18-August-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Girard's is the rule `reduce` runs, and this line is the whole of that
choice: any other would discharge it too. -/
theorem Zonotope.reduce_outer (Z : Zonotope (Vec 𝕋 n)) (o : ℕ) :
    Z.construct ⊆ (Z.reduce o).construct :=
  Zonotope.reduceGirard_outer Z o

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
