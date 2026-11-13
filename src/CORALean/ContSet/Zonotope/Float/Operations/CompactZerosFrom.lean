module

public import CORALean.ContSet.Zonotope.Float.Zonotope
public import Mathlib.Data.Finset.Sort
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `Zonotope.compactZerosFrom`, over a floating-point scalar

CORA's `compact_(Z, 'zeros')` at tolerance `0`, except that the first `s` generator columns are
kept whatever they are: the columns that are certifiably zero (`Zonotope.step_keepColumnFrom`, by
the certified `le` in both directions) from index `s` on are dropped, the others stay in order. It
drops the zeros of a network's image beyond the generators of its argument, which are the ones
that must stay in front. The center and the error box are copied; nothing rounds.

## Inputs
* `s` – number of leading columns kept
* `Z` – zonotope

## Output
* zonotope without certifiably zero generators from index `s` on
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- Whether column `j` is among the first `s`, or not certified zero. -/
@[step_of Zonotope.compactZerosFrom]
def Zonotope.step_keepColumnFrom (s : ℕ) (Z : Zonotope (Vec 𝕋 n)) (j : Fin Z.h) : Bool :=
  Nat.blt j.val s || !(List.finRange n).all fun i => le (Z.G j i) zero && le zero (Z.G j i)


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.compactZerosFrom (s : ℕ) (Z : Zonotope (Vec 𝕋 n)) : Zonotope (Vec 𝕋 n) where
  h := (Finset.univ.filter fun j => Z.step_keepColumnFrom s j = true).card
  c := Z.c
  G := fun j =>
    Z.G ((Finset.univ.filter fun j => Z.step_keepColumnFrom s j = true).orderEmbOfFin rfl j)
  I_error := Z.I_error

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
