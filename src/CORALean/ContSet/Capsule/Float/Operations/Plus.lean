module

public import CORALean.ContSet.Capsule.Float.Capsule
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.Global.Float.Sqrt

@[expose] public section

/-!
# `Capsule.plus`

CORA's capsule-plus-capsule: the centers add, the longer generator is kept and the shorter one is
absorbed into the radius, `r = r₁ + r₂ + ‖g_short‖₂`, rounded up. Here the center is added
downward and what that costs, the exact sum less the stored center (between `0` and the gap to
`addUp`, per entry), goes into the error box, with the sum of the operands' boxes. The lengths are
compared on the squares rounded up, which is only a choice of branch: both branches enclose the
sum. `k` is the number of Newton steps of the roots (`Global/Float/Sqrt`).

## Inputs
* `k` – Newton steps for sqrt
* `C₁` – first capsule
* `C₂` – second capsule

## Output
* a capsule enclosing the Minkowski sum
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Capsule.plus (k : ℕ) (C₁ C₂ : Capsule 𝕋 n) : Capsule 𝕋 n :=
  let c := fun i => addDown (C₁.c i) (C₂.c i)
  -- the two boxes, and what storing the lower rounding of the center costs
  let I := (C₁.I_error.plus C₂.I_error).plus
    (Interval.residual c (fun i => addUp (C₁.c i) (C₂.c i)) c)
  if le (sqSumUp fun i => absolute (C₂.g i)) (sqSumUp fun i => absolute (C₁.g i)) then
    ⟨c, C₁.g, addUp (addUp C₁.r C₂.r) (normUp k C₂.g), I⟩
  else
    ⟨c, C₂.g, addUp (addUp C₁.r C₂.r) (normUp k C₁.g), I⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
