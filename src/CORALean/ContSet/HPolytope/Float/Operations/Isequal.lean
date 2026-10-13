import CORALean.ContSet.HPolytope.Float.HPolytope

/-!
# `HPolytope.isequal`, over a floating-point scalar

The structural test at tolerance `0`: the same numbers of inequalities and equalities, and the
matrices, the right-hand sides and the two ends of the equality interval equal entry by entry,
each by the certified `le` in both directions. Certified in one direction only: `true` is a
proof, `false` refutes nothing.
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

def HPolytope.isequal (P Q : HPolytope 𝕋 (Vec 𝕋 n)) : Bool :=
  if e : P.m = Q.m ∧ P.me = Q.me then
    (List.finRange P.m).all (fun r =>
      (le (P.b r) (Q.b (Fin.cast e.1 r)) && le (Q.b (Fin.cast e.1 r)) (P.b r)) &&
      (List.finRange n).all fun j =>
        le (P.A r j) (Q.A (Fin.cast e.1 r) j) && le (Q.A (Fin.cast e.1 r) j) (P.A r j)) &&
    (List.finRange P.me).all fun r =>
      (le (P.be.inf r) (Q.be.inf (Fin.cast e.2 r)) &&
        le (Q.be.inf (Fin.cast e.2 r)) (P.be.inf r)) &&
      (le (P.be.sup r) (Q.be.sup (Fin.cast e.2 r)) &&
        le (Q.be.sup (Fin.cast e.2 r)) (P.be.sup r)) &&
      (List.finRange n).all fun j =>
        le (P.Ae r j) (Q.Ae (Fin.cast e.2 r) j) && le (Q.Ae (Fin.cast e.2 r) j) (P.Ae r j)
  else false

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
