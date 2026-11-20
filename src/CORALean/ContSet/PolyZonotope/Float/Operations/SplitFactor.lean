module

public import CORALean.ContSet.PolyZonotope.Float.Operations.GetSubset
public import CORALean.ContSet.PolyZonotope.Float.Operations.Pick
public import CORALean.ContSet.PolyZonotope.Float.Operations.FoldConstants

@[expose] public section

/-!
# `PolyZonotope.splitFactor`

CORA's `splitDepFactor` as CORA.cpp computes it: the factor `k` restricted to `[0, 1]` and to
`[-1, 0]`, each half the substitution `αₖ = ±1/2 + β/2` (`PolyZonotope.getSubset`). The columns of
a half are taken in CORA.cpp's order (first the generators without the factor, then for each
exponent `i` of it and each `m ≤ i` the generators of that exponent), the columns without any
factor go into the center (`PolyZonotope.foldConstants`). CORA's constructor, which merges
equal exponent columns, is left to the caller (`PolyZonotope.construct`).

## Inputs
* `pZ` – polynomial zonotope
* `k` – factor to split

## Output
* the half where the factor is in `[0, 1]`, and the half where it is in `[-1, 0]`
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

def PolyZonotope.splitFactor (pZ : PolyZonotope (Vec 𝕋 n)) (k : Fin pZ.p) :
    PolyZonotope (Vec 𝕋 n) × PolyZonotope (Vec 𝕋 n) :=
  -- the highest exponent of the factor; column `(j, m)` of a subset is `m + (N + 1) j`
  let N := pZ.maxExp k
  let gens := fun i : ℕ => (List.finRange pZ.h).filter fun j => pZ.E k j == i
  let cols : List ℕ := (gens 0).map (fun j => (N + 1) * j.val) ++
    (List.range N).flatMap fun i => (List.range (i + 2)).flatMap fun m =>
      (gens (i + 1)).map fun j => m + (N + 1) * j.val
  -- each half: its columns in that order, the constants in the center
  let piece := fun cen : 𝕋 =>
    ((pZ.getSubset k cen (half one)).pick cols.length fun t => cols[t.val]!).foldConstants
  (piece (half one), piece (neg (half one)))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
