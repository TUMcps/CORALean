module

public import CORALean.ContSet.Ellipsoid.Float.Ellipsoid

@[expose] public section

/-!
# `Ellipsoid.isequal`, over a floating-point scalar

The structural test at tolerance `0`, as over ℝ: the same number of generators, and the centre,
the generator matrix and the two ends of the error box equal entry by entry, each by the certified
`le` in both directions. Certified in one direction only: `true` is a proof, `false` refutes
nothing. Stricter than CORA's test on `Q = G Gᵀ`.
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

def Ellipsoid.isequal (E S : Ellipsoid 𝕋 n) : Bool :=
  if e : E.k = S.k then
    (List.finRange n).all (fun i =>
      (le (E.c i) (S.c i) && le (S.c i) (E.c i)) &&
      (le (E.I_error.inf i) (S.I_error.inf i) && le (S.I_error.inf i) (E.I_error.inf i)) &&
      (le (E.I_error.sup i) (S.I_error.sup i) && le (S.I_error.sup i) (E.I_error.sup i)) &&
      (List.finRange E.k).all fun j =>
        le (E.G i j) (S.G i (Fin.cast e j)) && le (S.G i (Fin.cast e j)) (E.G i j))
  else false

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
