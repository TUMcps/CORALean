import CORALean.ContSet.ConZonotope.Float.ConZonotope
import CORALean.ContSet.HPolytope.Float.Operations.Isequal

/-!
# `ConZonotope.isequal`, over a floating-point scalar

The structural test at tolerance `0`, as over ℝ: the same number of generators, the centre, the
generators and the two ends of the error box equal entry by entry, each by the certified `le` in
both directions, and the constraint polytopes `HPolytope.isequal`. Certified in one direction
only: `true` is a proof, `false` refutes nothing. Not CORA's test, which compares up to the order
of the columns and falls back to the vertices.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConZonotope.isequal (Z S : ConZonotope 𝕋 n) : Bool :=
  if e : Z.h = S.h then
    (List.finRange n).all (fun i =>
      (le (Z.c i) (S.c i) && le (S.c i) (Z.c i)) &&
      (le (Z.E.inf i) (S.E.inf i) && le (S.E.inf i) (Z.E.inf i)) &&
      (le (Z.E.sup i) (S.E.sup i) && le (S.E.sup i) (Z.E.sup i)) &&
      (List.finRange Z.h).all fun j =>
        le (Z.G j i) (S.G (Fin.cast e j) i) && le (S.G (Fin.cast e j) i) (Z.G j i)) &&
    HPolytope.isequal Z.P (e ▸ S.P)
  else false

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
