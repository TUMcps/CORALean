import CORALean.ContSet.Ellipsoid.Float.Ellipsoid

/-!
# `Ellipsoid.isequal`, over a floating-point scalar

The structural test at tolerance `0`, as over ℝ: the same number of generators, and the centre,
the generator matrix and the two ends of the error box equal entry by entry, each by the certified
`le` in both directions. Certified in one direction only: `true` is a proof, `false` refutes
nothing. Stricter than CORA's test on `Q = G Gᵀ`.
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

def Ellipsoid.isequal (E S : Ellipsoid 𝕋 n) : Bool :=
  if e : E.k = S.k then
    (List.finRange n).all (fun i =>
      (le (E.q i) (S.q i) && le (S.q i) (E.q i)) &&
      (le (E.err.inf i) (S.err.inf i) && le (S.err.inf i) (E.err.inf i)) &&
      (le (E.err.sup i) (S.err.sup i) && le (S.err.sup i) (E.err.sup i)) &&
      (List.finRange E.k).all fun j =>
        le (E.G i j) (S.G i (Fin.cast e j)) && le (S.G i (Fin.cast e j)) (E.G i j))
  else false

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
