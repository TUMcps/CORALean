module

public import CORALean.ContSet.PolyZonotope.Real.PolyZonotope

@[expose] public section

/-!
# `ConPolyZono.unitCol`

One column of an exponent matrix, reading a single factor to the power `e` and
no other factor at all. The building block every column of the union's selector
constraint in [1, Thm. 1] is assembled from, by adding such columns.

`PolyZonotope.identE` is the same shape at `e = 1`, but as a whole square matrix
rather than as a column, which is what an assembly needs.

## Inputs
* `p` – number of factors
* `i` – factor index
* `e` – exponent

## Output
* exponent column with that exponent at the factor

## References

* [1] [N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta Informatica,
      2023.](../../../../../../references/2023/kochdumper-constrained-polyzonotopes.md)
-/

-- Authors:       Claude Opus 5
-- Written:       13-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The exponent column with `e` at factor `i` and zero everywhere else. -/
def ConPolyZono.unitCol {p : ℕ} (i : Fin p) (e : ℕ) : Fin p → ℕ :=
  fun k => if k = i then e else 0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
