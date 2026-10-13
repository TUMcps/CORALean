import CORALean.ContSet.Zonotope.Float.Operations.MinnormOffset

/-!
# `Zonotope.minnorm`, over a floating-point scalar

CORA's `minnorm(Z)` [2]: the smallest offset of the facets of `polytope(Z - c)`, rows normalized to
unit length, which is the distance from the centre to the boundary. Rounded up, it is an upper
bound on the radius of every Euclidean ball around the centre inside the zonotope the stored
floats describe (`Zonotope.minnorm_ball`), and on the exact `minnorm` when the generators span
(`Zonotope.minnorm_le`). Only the upper side is computed: the lower side would need the facet
normals exactly.

The minimum runs over the `n`-subsets of generators in increasing index order
(`List.sublistsLen`), where the exact layer's runs over every selection `Fin n → Fin h`; a
permutation of a subset gives the same row up to sign, and a repeated generator a zero row, which
CORA removes as `NaN`. `none` where no subset gives a row. The facet rows are the cross products of
`n` generators [1, Thm. 2]. The second output of CORA, the foot point `x`, is not computed.

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes".
      arXiv, 2015.
* [2] `contSet/@zonotope/minnorm.m`, CORA (Sep. 2025).
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


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
