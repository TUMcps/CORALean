module

public import CORALean.ContSet.Capsule.Float.Capsule

@[expose] public section

/-!
# `Capsule.representsa_point`, over a floating-point scalar

`@capsule/representsa_.m` at `point`, tolerance `0`: no direction, no radius, and an error box
that is the origin (CORA's capsule has no box). Each stored value is compared with `zero` both
ways by the certified `le`, so `true` is a proof and `false` refutes nothing.
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

def Capsule.representsa_point (C : Capsule 𝕋 n) : Bool :=
  (List.finRange n).all (fun i => le (C.g i) zero && le zero (C.g i)) &&
    le C.r zero && le zero C.r &&
    (List.finRange n).all (fun i => le (C.I_error.inf i) zero && le zero (C.I_error.inf i) &&
      le (C.I_error.sup i) zero && le zero (C.I_error.sup i))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
