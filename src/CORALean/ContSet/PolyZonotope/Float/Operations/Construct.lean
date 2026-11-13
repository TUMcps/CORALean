module

public import CORALean.ContSet.PolyZonotope.Float.Operations.CompactGens
public import CORALean.ContSet.PolyZonotope.Float.Operations.KeepIdx
public import CORALean.ContSet.PolyZonotope.Float.Operations.Pick

@[expose] public section

/-!
# `PolyZonotope.construct`

CORA's `polyZonotope(c, G, GI, E, id)` on the dependent part: the generators that are zero go
(`pick`), equal exponent columns are added (`compactGens`, the sum of a class from the last column
to the first), and the merged columns come in the order `order` names. CORA's is the order of a
random hash of the exponent columns, which is computed outside Lean (`Examples/Oracle`): `order`
gets the number of identifiers and the exponent columns, and answers the first column of each
class in the order wanted. Any answer is sound, a wrong one costing nothing but the order (`pick`).

## Inputs
* `pZ` – polynomial zonotope
* `order` – the order of the merged classes

## Output
* polynomial zonotope without zero generators and with distinct exponent columns
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's constructor: the zero generators dropped, the equal exponent columns added, the
columns in the order of `order`. -/
def PolyZonotope.construct (pZ : PolyZonotope (Vec 𝕋 n))
    (order : ℕ → Array (Array ℕ) → Array ℕ) : PolyZonotope (Vec 𝕋 n) :=
  -- `live`: the generators that are not zero
  let live : Array ℕ := ((List.finRange pZ.h).filter fun l =>
    !(List.finRange n).all fun i => le (pZ.G l i) zero && le zero (pZ.G l i)).toArray.map Fin.val
  let P := pZ.pick live.size fun t => live[t.val]!
  -- the classes of equal columns merged, each class by the first column in it
  let M := P.compactGens
  let reps : Array ℕ := Array.ofFn fun j : Fin M.h => (PolyZonotope.keepIdx P.E j).val
  let cols : Array (Array ℕ) := Array.ofFn fun l : Fin P.h => Array.ofFn fun k : Fin P.p => P.E k l
  let ks : Array ℕ := (order P.p cols).filterMap fun f => reps.findIdx? (· == f)
  M.pick ks.size fun t => ks[t.val]!

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
