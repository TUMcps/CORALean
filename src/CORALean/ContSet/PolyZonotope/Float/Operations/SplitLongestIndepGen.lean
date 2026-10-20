module

public import CORALean.ContSet.PolyZonotope.Float.Operations.SplitIndepGen

@[expose] public section

/-!
# `PolyZonotope.splitLongestIndepGen`, over a floating-point scalar

The subfunction `aux_splitLongestIndepGen` of CORA's `@polyZonotope/containsPointSet`: the
independent generator of largest `Σᵢ GI(i,j)²`, rounded up and the first of equal ones winning,
halved by `splitIndepGen`; the set twice where there is no independent generator. Any generator
is sound for the split, so a misranking costs precision alone.

## Inputs
* `pZ` – polynomial zonotope

## Output
* pair of polynomial zonotopes from halving the longest independent generator
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.splitLongestIndepGen (pZ : PolyZonotope (Vec 𝕋 n)) :
    PolyZonotope (Vec 𝕋 n) × PolyZonotope (Vec 𝕋 n) :=
  -- len = sum(GI.^2, 1)
  let len := fun j => sumUp fun i => mulUp (pZ.GI j i) (pZ.GI j i)
  -- [~, ind] = max(len)
  match (List.finRange pZ.q).foldl
      (fun best j => match best with
        | none => some j
        | some b => if le (len j) (len b) then some b else some j)
      none with
  | some j => pZ.splitIndepGen j
  | none => (pZ, pZ)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
