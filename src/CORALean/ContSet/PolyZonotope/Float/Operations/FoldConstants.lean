module

public import CORALean.ContSet.PolyZonotope.Float.PolyZonotope

@[expose] public section

/-!
# `PolyZonotope.foldConstants`

CORA.cpp's `priv_fold_constants`: the dependent generators with no factor (their monomial is one)
added into the center in their order, each sum stored rounded up and its width added to the error
box; the other generators kept in their order. After CORA's constructor there is at most one such
generator, and at `nearest` the center is then `c + g`.

## Inputs
* `pZ` – polynomial zonotope

## Output
* polynomial zonotope without constant dependent generators
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

/-- The dependent generators with no factor (their monomial is one) added into the center in
their order, each sum stored rounded up and its width added to the error box; the other
generators kept in their order. -/
def PolyZonotope.foldConstants (pZ : PolyZonotope (Vec 𝕋 n)) : PolyZonotope (Vec 𝕋 n) :=
  -- the generators without a factor, and the others
  let isConst : Fin pZ.h → Bool := fun l => (List.finRange pZ.p).all fun k => pZ.E k l == 0
  let K := (List.finRange pZ.h).filter isConst
  let keep : Array (Fin pZ.h) := (Array.ofFn id).filter fun l => !isConst l
  -- the constants added to the center in order, with the widths of the sums
  let S : Fin n → 𝕋 × 𝕋 := fun i => K.foldl (fun acc l =>
    (addUp acc.1 (pZ.G l i), addUp acc.2 (subUp (addUp acc.1 (pZ.G l i))
      (addDown acc.1 (pZ.G l i))))) (pZ.c i, zero)
  { pZ with
    c := fun i => (S i).1
    h := keep.size
    G := fun t => pZ.G (keep[t.val]'t.isLt)
    E := fun k t => pZ.E k (keep[t.val]'t.isLt)
    I_error := ⟨fun i => subDown (pZ.I_error.inf i) (S i).2,
      fun i => addUp (pZ.I_error.sup i) (S i).2⟩ }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
