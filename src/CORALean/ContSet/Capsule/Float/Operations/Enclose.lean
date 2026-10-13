import CORALean.ContSet.Capsule.Float.Operations.ConvHull
import CORALean.ContSet.Capsule.Float.Operations.Mtimes

/-!
# `Capsule.enclose`, over a floating-point scalar

CORA's `@capsule/enclose.m` with a matrix, as the exact layer reads it: `C2 = M * Cplus`, then
`convHull(C, C2)`. The header documents `M C + Cplus`, which the code does not compute (see
`Capsule.enclose_cora_counterexample`); the generic `ContSet.enclose` is the documented set, which
the `Plus`, `Mtimes` and `LinComb` instances of this class now give at float too.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Capsule.enclose (k : ℕ) (C : Capsule 𝕋 n) (M : Mat 𝕋 n m) (Cplus : Capsule 𝕋 m) :
    Capsule 𝕋 n :=
  let C2 := Capsule.mtimes k M Cplus
  C.convHull k C2

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
