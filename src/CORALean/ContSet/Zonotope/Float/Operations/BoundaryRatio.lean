module

public import CORALean.ContSet.Zonotope.Float.Operations.BoundaryRatioAt

@[expose] public section

/-!
# `Zonotope.boundaryRatio`, over a floating-point scalar

The exit step of `boundaryPoint`, as an upper bound: the least of the facet rows' bounds
(`boundaryRatioAt`) over the subsets of `n` generators in increasing index order
(`List.sublistsLen`); a permutation of a subset gives the same row up to sign, and a repeated
generator a zero row, which has no certified positive denominator. Every row bounds the exact step,
so the minimum does, whichever rows are present. `none` where no subset gives a row. Only the upper
side is computed: the lower side would need a feasible point of the linear program.

## Inputs
* `Z` – zonotope
* `dir` – direction
* `start` – starting point

## Output
* least bound on the exit step over the facet rows, if any
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The least of the facet rows' bounds on the exit step. -/
def Zonotope.boundaryRatio (Z : Zonotope (Vec 𝕋 (n + 1))) (dir start : Vec 𝕋 (n + 1)) :
    Option 𝕋 :=
  let b := (List.sublistsLen n (List.finRange Z.h)).filterMap fun T =>      -- one row per subset
    if hT : T.length = n then Z.boundaryRatioAt dir start fun k => T.get (k.cast hT.symm)
    else none
  b.foldl (fun best o => match best with                                   -- min(b)
    | none => some o
    | some x => some (minimum x o)) none

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
