module

public import CORALean.ContSet.Zonotope.Float.Zonotope

@[expose] public section

/-!
# `Zonotope.longestGen`, over a floating-point scalar

The index CORA's `splitLongestGen` splits at: `len = sum(G.^2, 1)` and `[~,ind] = max(len)`.
The squared lengths are `sumUp` of `mulUp` squares, and the argmax is a left fold over the
generator indices that keeps the running best unless a later length is not known to be `≤` it,
so a tie keeps the first. `le` has no order laws, so this is a ranking, not a `List.argmax`;
every index is a sound place to split, so a misranking costs precision alone. `none` when there
is no generator, where CORA splits nothing either.

## Inputs
* `Z` – zonotope

## Output
* first generator of maximal squared length, if any
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The first generator of `Z` whose squared length `Σᵢ G(i,j)²` is maximal. -/
def Zonotope.longestGen (Z : Zonotope (Vec 𝕋 n)) : Option (Fin Z.h) :=
  let len := fun j => sumUp fun i => mulUp (Z.G j i) (Z.G j i)
  (List.finRange Z.h).foldl
    (fun best j => match best with
      | none => some j
      | some b => if le (len j) (len b) then some b else some j)
    none

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
