module

public import CORALean.ContSet.Capsule.Float.Capsule
public import CORALean.Global.Float.Sqrt

@[expose] public section

/-!
# `Capsule.radius`

CORA's `norm(g, 2) + r` with the norm rounded up: `normUp` of the generator, added to the radius
upward. `k` is the number of Newton steps of the root (`Global/Float/Sqrt`).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Capsule.radius (k : ℕ) (C : Capsule 𝕋 n) : 𝕋 :=
  let length := normUp k C.g
  addUp length C.r

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
