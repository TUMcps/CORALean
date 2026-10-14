module

public import CORALean.ContSet.Capsule.Float.Capsule

@[expose] public section

/-!
# `Capsule.representsa_point`, over a floating-point scalar

`@capsule/representsa_.m` at `point`, tolerance `0`: no direction and no radius. Each stored value
is compared with `zero` both ways by the certified `le`, so `true` is a proof and `false` refutes
nothing.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Capsule.representsa_point (C : Capsule 𝕋 n) : Bool :=
  (List.finRange n).all (fun i => le (C.g i) zero && le zero (C.g i)) &&
    le C.r zero && le zero C.r

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
