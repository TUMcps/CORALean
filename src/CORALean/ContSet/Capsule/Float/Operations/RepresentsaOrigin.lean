import CORALean.ContSet.Capsule.Float.Operations.RepresentsaPoint

/-!
# `Capsule.representsa_origin`, over a floating-point scalar

`@capsule/representsa_.m` at `origin`, tolerance `0`: a point whose centre is `0`.
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

def Capsule.representsa_origin (C : Capsule 𝕋 n) : Bool :=
  (List.finRange n).all (fun i => le (C.c i) zero && le zero (C.c i)) && C.representsa_point

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
