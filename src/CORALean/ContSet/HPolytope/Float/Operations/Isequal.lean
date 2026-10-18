module

public import CORALean.ContSet.HPolytope.Float.HPolytope

@[expose] public section

/-!
# `HPolytope.isequal`, over a floating-point scalar

The structural test at tolerance `0`: the same numbers of inequalities and equalities, and the
matrices, the right-hand sides, their slacks and the two ends of the error box equal entry by entry,
each by the certified `le` in both directions. Certified in one direction only: `true` is a
proof, `false` refutes nothing.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       03-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.isequal (P Q : HPolytope 𝕋 (Vec 𝕋 n)) : Bool :=
  if e : P.m = Q.m ∧ P.me = Q.me then
    (List.finRange P.m).all (fun r =>
      ((le (P.b r) (Q.b (Fin.cast e.1 r)) && le (Q.b (Fin.cast e.1 r)) (P.b r)) &&
        (le (P.b_error r) (Q.b_error (Fin.cast e.1 r)) &&
          le (Q.b_error (Fin.cast e.1 r)) (P.b_error r))) &&
      (List.finRange n).all fun j =>
        le (P.A r j) (Q.A (Fin.cast e.1 r) j) && le (Q.A (Fin.cast e.1 r) j) (P.A r j)) &&
    (List.finRange P.me).all (fun r =>
      ((le (P.be r) (Q.be (Fin.cast e.2 r)) && le (Q.be (Fin.cast e.2 r)) (P.be r)) &&
        (le (P.be_error r) (Q.be_error (Fin.cast e.2 r)) &&
          le (Q.be_error (Fin.cast e.2 r)) (P.be_error r))) &&
      (List.finRange n).all fun j =>
        le (P.Ae r j) (Q.Ae (Fin.cast e.2 r) j) && le (Q.Ae (Fin.cast e.2 r) j) (P.Ae r j)) &&
    (List.finRange n).all fun j =>
      (le (P.I_error.inf j) (Q.I_error.inf j) && le (Q.I_error.inf j) (P.I_error.inf j)) &&
      (le (P.I_error.sup j) (Q.I_error.sup j) && le (Q.I_error.sup j) (P.I_error.sup j))
  else false

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
