module

public import CORALean.ContSet.Zonotope.Float.Operations.GirardSplit
public import CORALean.ContSet.Zonotope.Float.Operations.ReduceByBox

@[expose] public section

/-!
# `Zonotope.reduceGirardBox`

The error `reduceGirard` pays, computed in `𝕋`: `reduceByBox` at the partition
`girardSplit` picks, and the degenerate `0` box where the order is already met
and nothing is dropped. So `reduceGirard Z o` reaches no further than `Z` plus
this, which is the reverse of `reduceGirard_outer`.

Not a `Reduce` operation and no class instantiates it: `Reduce` obliges the
outer direction only, while a box for the reverse one is a fact about the
particular rule `reduce` runs.

## Inputs
* `Z` – zonotope
* `o` – target order

## Output
* box absorbing the generators Girard's rule drops
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The box `reduceGirard` absorbs the dropped generators into, on its own —
and the degenerate `0` box at an order already met, where nothing is dropped. -/
def Zonotope.reduceGirardBox (Z : Zonotope (Vec 𝕋 n)) (o : ℕ) : Zonotope (Vec 𝕋 n) :=
  if hlt : o * n < Z.h then Z.reduceByBox (Z.girardSplit o hlt)
  else ⟨n, fun _ => zero, fun _ _ => zero, ⟨fun _ => zero, fun _ => zero⟩⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
