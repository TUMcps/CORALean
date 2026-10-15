module

public import CORALean.ContSet.ConPolyZono.Float.ConPolyZono

@[expose] public section

/-!
# `ConPolyZono.isequal`, over a floating-point scalar

The structural test at tolerance `0`, as over ℝ: the same numbers of factors, generators and
constraints, the center, the generators, the exponent matrices, the constraint matrix, the two ends
of the constraint interval and of the error box equal, each stored number by the certified `le`
in both directions. Certified in one direction only: `true` is a proof, `false` refutes nothing.
Not CORA's test, which compacts and reorders first.
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

def ConPolyZono.isequal (Z S : ConPolyZono 𝕋 (Vec 𝕋 n)) : Bool :=
  if e : Z.p = S.p ∧ Z.h = S.h ∧ Z.qI = S.qI ∧ Z.m = S.m ∧ Z.q = S.q then
    -- the center, the error box and the two generator blocks, entry by entry
    (List.finRange n).all (fun i =>
      (le (Z.c i) (S.c i) && le (S.c i) (Z.c i)) &&
      (le (Z.I_error.inf i) (S.I_error.inf i) && le (S.I_error.inf i) (Z.I_error.inf i)) &&
      (le (Z.I_error.sup i) (S.I_error.sup i) && le (S.I_error.sup i) (Z.I_error.sup i)) &&
      (List.finRange Z.h).all (fun j =>
        le (Z.G j i) (S.G (Fin.cast e.2.1 j) i) && le (S.G (Fin.cast e.2.1 j) i) (Z.G j i)) &&
      (List.finRange Z.qI).all fun j =>
        le (Z.GI j i) (S.GI (Fin.cast e.2.2.1 j) i) &&
          le (S.GI (Fin.cast e.2.2.1 j) i) (Z.GI j i)) &&
    -- the constraint interval and matrix
    (List.finRange Z.m).all (fun r =>
      (le (Z.b.inf r) (S.b.inf (Fin.cast e.2.2.2.1 r)) &&
        le (S.b.inf (Fin.cast e.2.2.2.1 r)) (Z.b.inf r)) &&
      (le (Z.b.sup r) (S.b.sup (Fin.cast e.2.2.2.1 r)) &&
        le (S.b.sup (Fin.cast e.2.2.2.1 r)) (Z.b.sup r)) &&
      (List.finRange Z.q).all fun j =>
        le (Z.A r j) (S.A (Fin.cast e.2.2.2.1 r) (Fin.cast e.2.2.2.2 j)) &&
          le (S.A (Fin.cast e.2.2.2.1 r) (Fin.cast e.2.2.2.2 j)) (Z.A r j)) &&
    -- the exponent matrices of the generators and of the constraints
    (List.finRange Z.p).all (fun k =>
      (List.finRange Z.h).all (fun j =>
        Z.E k j == S.E (Fin.cast e.1 k) (Fin.cast e.2.1 j)) &&
      (List.finRange Z.q).all fun j =>
        Z.R k j == S.R (Fin.cast e.1 k) (Fin.cast e.2.2.2.2 j))
  else false

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
