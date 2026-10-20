module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Rep

@[expose] public section

/-!
# Equal columns have the same representative

`rep` is a `min'` over the columns equal to a given one, so it reads its
argument only through `col`. Splitting the two generators of a class is
therefore impossible, which is what `merge` needs in both directions: a dropped
column gathers nothing, and two kept columns differ.

## Inputs
* `p` – number of factors
* `h` – number of generators
* `E` – exponent matrix
* `i` – first generator index
* `j` – second generator index

## Hypotheses
* `hij` – their exponent columns are equal

## Conclusion
* both have the same representative
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.rep_congr {p h : ℕ} (E : Fin p → Fin h → ℕ) {i j : Fin h}
    (hij : PolyZonotope.col E i = PolyZonotope.col E j) :
    PolyZonotope.rep E i = PolyZonotope.rep E j := by
  simp only [PolyZonotope.rep, hij]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
