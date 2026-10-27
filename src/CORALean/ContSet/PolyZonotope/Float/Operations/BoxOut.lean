module

public import CORALean.ContSet.PolyZonotope.Float.PolyZonotope
public import Mathlib.Data.Finset.Sort
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `PolyZonotope.boxOut`, over a floating-point scalar

The tail of CORA's `outerApprox`: the `removed` dependent generators leave `G` and `E` for a
diagonal box appended to the independent block, which also covers the `taken` independent ones.
The radius is `step_boxOutRadius`, at least the exact one; center, error box and the kept columns
are copied, the kept columns being read off in order by `orderEmbOfFin`.

## Inputs
* `pZ` – polynomial zonotope
* `removed` – mask of dependent generators removed
* `taken` – mask of independent generators taken

## Output
* polynomial zonotope with the masked generators moved into a box
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- The radius of the box in coordinate `i`, rounded up. -/
@[step_of PolyZonotope.boxOut]
def PolyZonotope.step_boxOutRadius (pZ : PolyZonotope (Vec 𝕋 n)) (removed : Fin pZ.h → Bool)
    (taken : Fin pZ.q → Bool) : Vec 𝕋 n := fun i =>
  addUp (sumUp fun l => if removed l then absolute (pZ.G l i) else zero)
    (sumUp fun j => if taken j then absolute (pZ.GI j i) else zero)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `pZ` without the `removed` dependent generators, and the box of those and of the `taken`
independent ones appended to the independent block. -/
def PolyZonotope.boxOut (pZ : PolyZonotope (Vec 𝕋 n)) (removed : Fin pZ.h → Bool)
    (taken : Fin pZ.q → Bool) : PolyZonotope (Vec 𝕋 n) where
  p := pZ.p
  h := (Finset.univ.filter fun l => removed l = false).card
  q := pZ.q + n
  c := pZ.c
  G := fun l => pZ.G ((Finset.univ.filter fun l => removed l = false).orderEmbOfFin rfl l)
  E := fun k l => pZ.E k ((Finset.univ.filter fun l => removed l = false).orderEmbOfFin rfl l)
  GI := Fin.append pZ.GI fun j i => diagonalBlock (pZ.step_boxOutRadius removed taken) i j
  I_error := pZ.I_error

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
