module

public import CORALean.ContSet.PolyZonotope.Float.Theorems.CompactOuter
public import CORALean.ContSet.PolyZonotope.Float.Theorems.ReduceGirardOuter

@[expose] public section

/-!
# `PolyZonotope.reduce` over-approximates the set

`compact` first, then `reduceGirard` — Girard's is the rule `reduce` runs, and
this composition is the whole of that choice: any other rule would discharge it
too.

## Inputs
* `pZ` – polynomial zonotope
* `o` – target order

## Hypotheses
* none

## Conclusion
* the set is contained in the result
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Girard's is the rule `reduce` runs, and this line is the whole of that
choice: any other would discharge it too. -/
theorem PolyZonotope.reduce_outer (pZ : PolyZonotope (Vec 𝕋 n)) (o : ℕ) :
    pZ.construct ⊆ (pZ.reduce o).construct :=
  subset_trans (PolyZonotope.compact_outer pZ)
    (PolyZonotope.reduceGirard_outer pZ.compact o)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
