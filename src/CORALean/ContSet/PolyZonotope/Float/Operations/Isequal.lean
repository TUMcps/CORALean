import CORALean.ContSet.PolyZonotope.Float.PolyZonotope

/-!
# `PolyZonotope.isequal`, over a floating-point scalar

The structural test at tolerance `0`, as over ℝ: the same numbers of factors and generators, the
centre, the generators, the exponent matrix and the two ends of the error box equal, each stored
number by the certified `le` in both directions. Certified in one direction only: `true` is a
proof, `false` refutes nothing. Not CORA's test, which compacts and reorders first.
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

def PolyZonotope.isequal (Z S : PolyZonotope 𝕋 n) : Bool :=
  if e : Z.p = S.p ∧ Z.h = S.h ∧ Z.q = S.q then
    (List.finRange n).all (fun i =>
      (le (Z.c i) (S.c i) && le (S.c i) (Z.c i)) &&
      (le (Z.err.inf i) (S.err.inf i) && le (S.err.inf i) (Z.err.inf i)) &&
      (le (Z.err.sup i) (S.err.sup i) && le (S.err.sup i) (Z.err.sup i)) &&
      (List.finRange Z.h).all (fun j =>
        le (Z.G i j) (S.G i (Fin.cast e.2.1 j)) && le (S.G i (Fin.cast e.2.1 j)) (Z.G i j)) &&
      (List.finRange Z.q).all fun j =>
        le (Z.GI i j) (S.GI i (Fin.cast e.2.2 j)) && le (S.GI i (Fin.cast e.2.2 j)) (Z.GI i j)) &&
    -- the exponent matrices
    (List.finRange Z.p).all fun k => (List.finRange Z.h).all fun j =>
      Z.E k j == S.E (Fin.cast e.1 k) (Fin.cast e.2.1 j)
  else false

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
