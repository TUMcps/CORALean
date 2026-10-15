module

public import Mathlib.Data.List.Range

@[expose] public section

/-!
# `Zonotope.reduceMatCora`: `reduce` of a matrix zonotope as CORA's code runs it

`@matZonotope/reduce.m` has the signature `reduce(matZ,option,order,filterLength)` and documents
the call `matZred = reduce(matZ,option,order)` (l. 4), with `filterLength - ?`. It passes
`filterLength` on unconditionally (l. 36, `reduce(Z, option, order, filterLength)`), so the
documented three-argument call stops with an unrecognized variable `filterLength`. A call with four
arguments gets to l. 39, `matZ = matZonotope(Zred)`, where `Zred` is a `zonotope`: MATLAB
dispatches to the method `contSet/@zonotope/matZonotope.m`, which stacks the generators as
`reshape(G,n,1,h)` and so returns a matrix zonotope of `n'` rows and one column, `n' = n·m`, not
the `n × m` one that was reduced (`zonotope(matZ)` stacked the entries, and nothing unstacks them).
Modelled: the number of arguments of the call, and the shape of the result. Read from the source,
not run.

# CORA's `reduce(matZonotope, ...)` throws, or changes the shape

`reduce(matZ,'girard',2)` of the `2 × 2` matrix zonotope `matZ` stops; with a fourth argument it
returns a `4 × 1` matrix zonotope.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- The model: CORA's code as printed, kept only to be refuted.
/-- `reduce(matZ, ...)` of an `n × m` matrix zonotope with `nargs` arguments in all: `none` is a
MATLAB error, otherwise the shape (rows, columns) of the matrix zonotope it returns. -/
def Zonotope.reduceMatCora (n m nargs : ℕ) : Option (ℕ × ℕ) :=
  if nargs = 4 then some (n * m, 1)     -- matZonotope(Zred): the (n·m) × 1 stacking
  else none                             -- filterLength (or order) is never assigned


-- =======================================  MAIN THEOREM  ======================================= --

/-- The documented call with three arguments stops. -/
theorem Zonotope.reduceMat_cora_counterexample (n m : ℕ) :
    Zonotope.reduceMatCora n m 3 = none := rfl

/-- A call that runs returns the wrong shape for every matrix zonotope with two or more columns. -/
theorem Zonotope.reduceMat_cora_shape_ne {n m : ℕ} (hm : 2 ≤ m) :
    Zonotope.reduceMatCora n m 4 ≠ some (n, m) := by
  simp only [Zonotope.reduceMatCora, if_true, ne_eq, Option.some.injEq, Prod.mk.injEq]
  omega

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
