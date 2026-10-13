module

public import CORALean.ContSet.Zonotope.Float.Operations.DetCandidate
public import CORALean.ContSet.Zonotope.Float.Zonotope

@[expose] public section

/-!
# `Zonotope.facetNormal`, over a floating-point scalar

[1, Thm. 2]'s normal at the `n` generators `S` selects: their `n`-dimensional cross product, the
alternating minors of the matrix holding them, one row dropped each time, as the exact layer's
`Zonotope.facetNormal` has it. Every minor is `Zonotope.detCandidate`, so the vector is a candidate
for the normal and not the normal: nothing downstream relies on it being one. `minnorm` bounds the
offset at *any* vector, which is why a rounded normal costs tightness and not soundness.

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes".
      arXiv, 2015.
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

/-- The cross product of the generators `S` selects, entry `i` being `(-1)^i` times the minor
without row `i`. -/
def Zonotope.facetNormal (Z : Zonotope (Vec 𝕋 (n + 1))) (S : Fin n → Fin Z.h) : Vec 𝕋 (n + 1) :=
  fun i =>
    let minor := Zonotope.detCandidate fun a b => Z.G (S b) (i.succAbove a)   -- H without row i
    if (i : ℕ) % 2 = 0 then minor else neg minor                              -- (-1)^i

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
