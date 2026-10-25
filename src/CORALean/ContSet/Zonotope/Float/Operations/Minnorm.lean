module

public import CORALean.ContSet.Zonotope.Float.Operations.MinnormOffset

@[expose] public section

/-!
# `Zonotope.minnorm`, over a floating-point scalar

CORA's `minnorm(Z)` [2]: the smallest offset of the facets of `polytope(Z - c)`, rows normalized to
unit length, the distance from the center to the boundary. Rounded up, it is an upper bound on the
radius of every Euclidean ball around the center inside the zonotope the stored floats describe
(`Zonotope.minnorm_ball`), and on the exact `minnorm` when the generators span
(`Zonotope.minnorm_le`). The minimum runs over the `n`-subsets of generators in increasing index
order (`List.sublistsLen`), where the exact layer's runs over every selection `Fin n → Fin h`; a
repeated generator gives a zero row, which CORA removes as `NaN`. `none` where no subset gives a
row. The facet rows are cross products of `n` generators [1, Thm. 2].

## Inputs
* `p` – Newton steps for the root
* `Z` – zonotope

## Output
* upper bound on the least facet offset, if any

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes". arXiv preprint
      arXiv:1512.02794, 2015.
* [2] `contSet/@zonotope/minnorm.m`, CORA (Sep. 2025).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `val = sqrt(min(b.^2))`, as an upper bound: the least rounded-up offset over the
subsets of `n` generators. -/
def Zonotope.minnorm (p : ℕ) (Z : Zonotope (Vec 𝕋 (n + 1))) : Option 𝕋 :=
  let b := (List.sublistsLen n (List.finRange Z.h)).filterMap fun T =>      -- b, one row per subset
    if hT : T.length = n then Z.minnormOffset p fun k => T.get (k.cast hT.symm) else none
  b.foldl (fun best o => match best with                                   -- min(b)
    | none => some o
    | some x => some (minimum x o)) none

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
