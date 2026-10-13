module

public import CORALean.ContSet.Zonotope.Float.Zonotope

@[expose] public section

/-!
# `Zonotope.isequal`, over a floating-point scalar

The structural test at tolerance `0`, as over ℝ: the same number of generators, and the centre,
the generators and the two ends of the error box equal entry by entry, each entry by the
certified `le` in both directions. Certified in one direction only: `true` is a proof, `false`
refutes nothing. Not CORA's test, which merges parallel generators and ignores their order.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.isequal (Z S : Zonotope (Vec 𝕋 n)) : Bool :=
  if e : Z.h = S.h then
    (List.finRange n).all (fun i =>
      (le (Z.c i) (S.c i) && le (S.c i) (Z.c i)) &&
      (le (Z.E.inf i) (S.E.inf i) && le (S.E.inf i) (Z.E.inf i)) &&
      (le (Z.E.sup i) (S.E.sup i) && le (S.E.sup i) (Z.E.sup i)) &&
      (List.finRange Z.h).all fun j =>
        le (Z.G j i) (S.G (Fin.cast e j) i) && le (S.G (Fin.cast e j) i) (Z.G j i))
  else false

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
