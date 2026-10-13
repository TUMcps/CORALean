module

public import CORALean.ContSet.ConPolyZono.Float.Theorems.CompactOuter
public import CORALean.ContSet.ConPolyZono.Float.Theorems.ReduceGirardOuter

@[expose] public section

/-!
# `ConPolyZono.reduce` encloses the set

Compaction, which encloses here where the exact layer's is an equality, followed
by Girard's rule, which is where every rounding of this operation already is.
Girard's is the rule `reduce` runs and this line is the whole of that choice:
any other ranking would discharge it too.
-/

-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.reduce_outer (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) (o : ℕ) :
    cPZ.construct ⊆ (cPZ.reduce o).construct :=
  subset_trans (ConPolyZono.compact_outer cPZ)
    (ConPolyZono.reduceGirard_outer cPZ.compact o)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
