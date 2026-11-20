module

public import CORALean.ContSet.PolyZonotope.Float.Operations.SplitFactor

@[expose] public section

/-!
# `PolyZonotope.splitLongest`

CORA's `splitLongestGen` as CORA.cpp computes it: the dependent generator of the largest squared
length (the products summed from zero in the order of the coordinates, the first of equal
lengths), its factor of the largest exponent (the first of equal ones), split by
`PolyZonotope.splitFactor`. `none` without a dependent generator or a factor.

## Inputs
* `pZ` – polynomial zonotope

## Output
* the two halves, or `none`
-/

-- Authors:       Claude Opus 5.5
-- Written:       20-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.splitLongest (pZ : PolyZonotope (Vec 𝕋 n)) :
    Option (PolyZonotope (Vec 𝕋 n) × PolyZonotope (Vec 𝕋 n)) :=
  -- the squared length of each generator, and the first longest one
  let len := fun j : Fin pZ.h =>
    (List.finRange n).foldl (fun acc r => addUp acc (mulUp (pZ.G j r) (pZ.G j r))) zero
  let longest := (List.finRange pZ.h).foldl (fun best j => match best with
    | none => some j
    | some b => if ltStrict (len b) (len j) then some j else some b) none
  -- its factor of the largest exponent
  match longest with
  | none => none
  | some j => ((List.finRange pZ.p).argmax fun k => pZ.E k j).map fun k => pZ.splitFactor k

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
