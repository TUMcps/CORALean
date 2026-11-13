module

public import CORALean.ContSet.Conversion.Float.Operations.PolyZonotope_to_Zonotope
public import CORALean.ContSet.PolyZonotope.Float.Operations.EvenShift
public import CORALean.ContSet.Zonotope.Float.Operations.Pick
public import CORALean.ContSet.Zonotope.Float.Operations.Plus

@[expose] public section

/-!
# CORA's `zonotope(pZ)`, the shift added to the center

`zonotopeEven` keeps the center and puts the sum of the shift terms into the error box. CORA's
`zonotope(pZ)` adds that sum to the center, `c = pZ.c + 0.5 * sum(Gquad, 2)`, so the float
center is the rounded sum. Here the sum of the terms is a zonotope without generators, whose center
is the sum rounded down and whose box is its gap, and the center is its `Zonotope.plus`. The
generators are those of `zonotopeEven`.

## Inputs
* `pZ` – polynomial zonotope

## Output
* zonotope with the shift in the center
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

/-- CORA's `zonotope(pZ)`: the generators in CORA's order `[G(:, ~isEvenColumn), 0.5 * Gquad, GI]`,
the center plus the rounded sum of the shift terms. A constant column is in the center whole and
has no generator, as in `zonotopeEven`. -/
def PolyZonotope.zonotopeFold (pZ : PolyZonotope (Vec 𝕋 n)) : Zonotope (Vec 𝕋 n) :=
  -- the odd columns, the even ones that are not constant, then the independent generators
  let idx : List ℕ :=
    ((List.finRange pZ.h).filter fun l =>
      !(List.finRange pZ.p).all fun k => pZ.E k l % 2 == 0).map Fin.val ++
    ((List.finRange pZ.h).filter fun l =>
      (List.finRange pZ.p).all (fun k => pZ.E k l % 2 == 0) &&
        !(List.finRange pZ.p).all fun k => pZ.E k l == 0).map Fin.val ++
    (List.range pZ.q).map (pZ.h + ·)
  -- `Z` of the generators about the old center, `Zs` the shift `0.5*sum(Gquad, 2)` as a point
  let Z : Zonotope (Vec 𝕋 n) := (⟨pZ.zonotopeEven.h, pZ.c, pZ.zonotopeEven.G, pZ.I_error⟩ :
    Zonotope (Vec 𝕋 n)).pick idx.length fun t => idx.getD t.val 0
  let Zs : Zonotope (Vec 𝕋 n) := ⟨0, fun i => sumDown fun l => pZ.evenShift l i, Fin.elim0,
    ⟨fun _ => zero, fun i => subUp (sumUp fun l => pZ.evenShift l i)
      (sumDown fun l => pZ.evenShift l i)⟩⟩
  Z.plus Zs

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
