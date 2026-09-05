import CORALean.ContSet.PolyZonotope.Float.Theorems.CompactOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.ReduceGirardOuter

/-!
# `PolyZonotope.reduce` over-approximates the set

`compact` first, then `reduceGirard` — Girard's is the rule `reduce` runs, and
this composition is the whole of that choice: any other rule would discharge it
too.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

/-- Girard's is the rule `reduce` runs, and this line is the whole of that
choice: any other would discharge it too. -/
theorem PolyZonotope.reduce_outer (PZ : PolyZonotope 𝕋 n) (o : ℕ) :
    PZ.construct ⊆ (PZ.reduce o).construct :=
  subset_trans (PolyZonotope.compact_outer PZ)
    (PolyZonotope.reduceGirard_outer PZ.compact o)

end CORALean.Float
