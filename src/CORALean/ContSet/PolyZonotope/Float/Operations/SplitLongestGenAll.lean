module

public import CORALean.ContSet.PolyZonotope.Float.Operations.SplitIndepGen
public import CORALean.ContSet.PolyZonotope.Float.Operations.SplitLongestGen

@[expose] public section

/-!
# `PolyZonotope.splitLongestGenAll`, over a floating-point scalar

CORA's `aux_splitLongestGen_` in `@polyZonotope/contains_`: the longest generator among the
dependent and the independent ones, by `sum([G, GI].^2, 1)` rounded up and the first of equal
ones winning, is split, a dependent one by `splitLongestGen`, an independent one by
`splitIndepGen`. With no generator at all the set is returned alone; CORA's `max` of an empty
row errors there.

## Inputs
* `pZ` – polynomial zonotope

## Output
* list of polynomial zonotopes from splitting the longest generator
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The pieces of `pZ` split along its longest generator, dependent or independent. -/
def PolyZonotope.splitLongestGenAll (pZ : PolyZonotope (Vec 𝕋 n)) : List (PolyZonotope (Vec 𝕋 n)) :=
  -- len = sum([pZ.G, pZ.GI].^2, 1)
  let len : Fin (pZ.h + pZ.q) → 𝕋 := Fin.append
    (fun l => sumUp fun i => mulUp (pZ.G l i) (pZ.G l i))
    (fun j => sumUp fun i => mulUp (pZ.GI j i) (pZ.GI j i))
  -- [~, ind] = max(len)
  match (List.finRange (pZ.h + pZ.q)).foldl (fun best l => match best with
    | none => some l
    | some b => if le (len l) (len b) then some b else some l) none with
  | none => [pZ]
  | some l =>
    if hl : l.val < pZ.h then [pZ.splitLongestGen.fst, pZ.splitLongestGen.snd]
    else [(pZ.splitIndepGen ⟨l.val - pZ.h, by have := l.isLt; omega⟩).fst,
      (pZ.splitIndepGen ⟨l.val - pZ.h, by have := l.isLt; omega⟩).snd]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
