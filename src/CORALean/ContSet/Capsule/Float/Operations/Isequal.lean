module

public import CORALean.ContSet.Capsule.Float.Capsule

@[expose] public section

/-!
# `Capsule.isequal`, over a floating-point scalar

`@capsule/isequal.m` at tolerance `0`, as the exact layer: center, generator and radius equal, and
the two error boxes have equal ends. The
scalar has no equality of its own, so each pair compares `≤` both ways by the certified `le`, whose
`true` is a proof and whose `false` refutes nothing.

## Inputs
* `C` – first capsule
* `S` – second capsule

## Output
* whether all fields are certified equal
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Capsule.isequal (C S : Capsule 𝕋 n) : Bool :=
  (List.finRange n).all (fun i => le (C.c i) (S.c i) && le (S.c i) (C.c i)) &&
    (List.finRange n).all (fun i => le (C.g i) (S.g i) && le (S.g i) (C.g i)) &&
    le C.r S.r && le S.r C.r &&
    (List.finRange n).all (fun i => le (C.I_error.inf i) (S.I_error.inf i) &&
      le (S.I_error.inf i) (C.I_error.inf i) && le (C.I_error.sup i) (S.I_error.sup i) &&
      le (S.I_error.sup i) (C.I_error.sup i))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
