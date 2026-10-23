module

public import CORALean.Specification.STLInterval.Operations.Basic
public import CORALean.Specification.STLInterval.Theorems.Basic

@[expose] public section

/-!
# An upper bound moved up, rounded up

Moving an upper bound up by `c` with `addUp` lands at least at the extended real moved by the real
`c`: `inf` stays `inf`, a stored bound is rounded up.

## Inputs
* `u` – upper bound
* `c` – number

## Hypotheses
* none

## Conclusion
* the rounded bound is at least the exact one
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem STLInterval.toEReal_map_addUp_ge (u : WithTop 𝕋) (c : 𝕋) : -- --- CONCL ---
    STLInterval.toEReal u + (toReal c : ℝ) ≤
      STLInterval.toEReal (u.map (addUp · c)) := by -- --- PROOF ---
  cases u with
  | top => simp
  | coe x =>
    simp only [WithTop.map_coe, STLInterval.toEReal_coe, ← EReal.coe_add, EReal.coe_le_coe_iff]
    exact add_le_addUp x c

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
