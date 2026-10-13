import CORALean.ContSet.PolyZonotope.Float.PolyZonotope

/-!
# `PolyZonotope.longestFactor`, over a floating-point scalar

The factor of highest exponent in the longest dependent generator, the length being `Σᵢ G(i,j)²`
rounded up and the first of equal ones winning, as over ℝ. Any factor is sound for the split
below, so a misranking costs precision alone.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.longestFactor (pZ : PolyZonotope (Vec 𝕋 n)) : Option (Fin pZ.p) :=
  -- the first generator whose squared length is maximal
  let len := fun j => sumUp fun i => mulUp (pZ.G j i) (pZ.G j i)
  match (List.finRange pZ.h).foldl
      (fun best j => match best with
        | none => some j
        | some b => if le (len j) (len b) then some b else some j)
      none with
  | some i => (List.finRange pZ.p).argmax (fun k => pZ.E k i)
  | none => none

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
