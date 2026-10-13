import CORALean.ContSet.Capsule.Float.Capsule
import CORALean.Global.Float.Sqrt

/-!
# `Capsule.plus`

CORA's capsule-plus-capsule: the centres add, the longer generator is kept and the shorter one is
absorbed into the radius, `r = r₁ + r₂ + ‖g_short‖₂`. Here the centre is added downward and the
distance of that stored centre from the exact sum (`‖c₁ + c₂ - c‖₂`, from the per-entry gap
between `addUp` and `addDown`) is added to the radius too, so the stored capsule holds the exact
one. The lengths are compared on the squares rounded up, which is only a choice of branch: both
branches enclose the sum. `k` is the number of Newton steps of the roots (`Global/Float/Sqrt`).
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

def Capsule.plus (k : ℕ) (C₁ C₂ : Capsule 𝕋 n) : Capsule 𝕋 n :=
  let c := fun i => addDown (C₁.c i) (C₂.c i)
  let gap := fun i => subUp (addUp (C₁.c i) (C₂.c i)) (c i)
  let rounding := normUp k gap
  if le (sqSumUp fun i => absolute (C₂.g i)) (sqSumUp fun i => absolute (C₁.g i)) then
    ⟨c, C₁.g, addUp (addUp (addUp C₁.r C₂.r) (normUp k C₂.g)) rounding⟩
  else
    ⟨c, C₂.g, addUp (addUp (addUp C₁.r C₂.r) (normUp k C₁.g)) rounding⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
