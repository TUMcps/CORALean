module

public import CORALean.ContSet.ConPolyZono.Float.ConPolyZono

@[expose] public section

/-!
# `ConPolyZono.longestFactor`, over a floating-point scalar

The factor `@conPolyZono/splitLongestGen` splits, by the exact layer's heuristic one step at a
time: drop the columns that are a single factor to the power one unless that would drop all of them,
halve the generators whose exponents are all even, measure each factor by the summed squared lengths
of the generators it appears in, rounded up, and take the first factor of largest measure. `none`
where there is no factor. Any factor is sound for the split, so a misranking costs precision alone.
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

def ConPolyZono.longestFactor (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) : Option (Fin cPZ.p) :=
  -- `indAll`: columns that are one factor to the power one and nothing else
  let indAll := Finset.univ.filter fun j : Fin cPZ.h =>
    ∃ i, ∑ j', cPZ.E i j' = 1 ∧ cPZ.E i j = 1 ∧ ∀ i', i' ≠ i → cPZ.E i' j = 0
  -- the columns kept, and `G` with the all-even columns halved
  let kept := if indAll.card < cPZ.h then indAllᶜ else Finset.univ
  let G := fun j c => if ∀ i, cPZ.E i j % 2 = 0 then half (cPZ.G j c) else cPZ.G j c
  -- `lenGen i`: the summed squared lengths of the generators carrying factor `i`, rounded up
  let lenGen := fun i : Fin cPZ.p => sumUp fun j : Fin cPZ.h =>
    if j ∈ kept ∧ 0 < cPZ.E i j then sumUp fun c => mulUp (G j c) (G j c) else zero
  -- the first factor whose measure is maximal
  (List.finRange cPZ.p).foldl
    (fun best i => match best with
      | none => some i
      | some b => if le (lenGen i) (lenGen b) then some b else some i)
    none

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
