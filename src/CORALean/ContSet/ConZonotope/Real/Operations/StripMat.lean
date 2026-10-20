module

public import CORALean.ContSet.ConZonotope.Real.ConZonotope

@[expose] public section

/-!
# `ConZonotope.stripMat`

The equality rows `C G ξ - φ ν = y - C c` that `ConZonotope.intersectStrip` appends, one per slab of
the strip: the first block reads the old factors through `C G`, the second pins the new factor `ν`
of slab `i` to `-φᵢ`.

## Inputs
* `cZ` – constrained zonotope
* `C` – strip direction matrix
* `φ` – strip half-widths

## Output
* the equality rows added for the strip
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n s : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The new equality rows `C G ξ - φ ν = y - C c`, one per slab. -/
def ConZonotope.stripMat (cZ : ConZonotope (Vec ℝ n)) (C : Mat ℝ s n) (φ : Vec ℝ s) :
    Mat ℝ s (cZ.h + s) :=
  fun i => Fin.append (fun j => (C *ᵥ cZ.G j) i) fun k => if k = i then -φ i else 0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
