module

public import CORALean.ContSet.ConPolyZono.Real.ConPolyZono
public import Mathlib.Data.List.MinMax

@[expose] public section

/-!
# `ConPolyZono.longestFactor`

The factor `@conPolyZono/splitLongestGen` splits, read off its heuristic one step at a time.
Drop the columns that are a single factor to the power one (a linear generator no other
factor touches), unless that would drop all of them; halve the generators whose exponents are
all even, which range over `[0, 1]` rather than `[-1, 1]`; measure each factor by the summed
squared lengths of the generators it appears in; take the first factor of largest measure.
`none` when there is no factor, where CORA's `max` of an empty vector errors.

Which factor is chosen never matters for the union of the halves.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The factor whose generators are longest, after CORA's two adjustments. -/
noncomputable def ConPolyZono.longestFactor (cPZ : ConPolyZono (Vec ℝ n)) :
    Option (Fin cPZ.p) :=
  -- `indAll`: columns that are one factor to the power one and nothing else
  let indAll := Finset.univ.filter fun j : Fin cPZ.h =>
    ∃ i, ∑ j', cPZ.E i j' = 1 ∧ cPZ.E i j = 1 ∧ ∀ i', i' ≠ i → cPZ.E i' j = 0
  -- the columns kept, and `G` with the all-even columns halved
  let kept := if indAll.card < cPZ.h then indAllᶜ else Finset.univ
  let G := fun j => if ∀ i, cPZ.E i j % 2 = 0 then (2 : ℝ)⁻¹ • cPZ.G j else cPZ.G j
  -- `lenGen i`: the summed squared lengths of the generators carrying factor `i`
  let lenGen := fun i : Fin cPZ.p =>
    ∑ j ∈ kept.filter fun j => 0 < cPZ.E i j, ∑ c, G j c ^ 2
  (List.finRange cPZ.p).argmax lenGen

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
