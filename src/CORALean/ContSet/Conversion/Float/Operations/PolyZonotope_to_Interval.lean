module

public import CORALean.ContSet.PolyZonotope.Float.Theorems.AbsLeErrorBound
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.PolyZonotope.Real.Theorems.AbsMonomialLeOne

@[expose] public section

/-!
# A polynomial zonotope as a box, over a floating-point scalar — the construction

`PolyZonotope.interval` is the construction; `PolyZonotope_to_Interval` states and proves what it
guarantees.
-/

-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The centre, then each block's reach in turn: three directed roundings rather
than one, so no intermediate sum is ever rounded the wrong way. -/
def PolyZonotope.interval (pZ : PolyZonotope (Vec 𝕋 n)) : Interval (Vec 𝕋 n) :=
  -- each block's reach, read off the generators laid out as CORA's `n × h` matrix
  let rG := radius fun i l => pZ.G l i
  let rGI := radius fun i j => pZ.GI j i
  { inf := fun i => subDown (subDown (subDown (pZ.c i) (rG i)) (rGI i))
      (PolyZonotope.errorBound pZ.I_error i)
    sup := fun i => addUp (addUp (addUp (pZ.c i) (rG i)) (rGI i))
      (PolyZonotope.errorBound pZ.I_error i) }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
