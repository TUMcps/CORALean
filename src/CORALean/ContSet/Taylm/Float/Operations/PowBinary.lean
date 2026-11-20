module

public import CORALean.ContSet.Taylm.Float.Operations.TimesMerged
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `Taylm.powBinary`

The natural power of a Taylor model as CORA.cpp's `Taylm::power` computes it: from the constant
model `1` of the model's order, binary exponentiation (`Taylm.step_powBinary`); the zeroth power is
`1`. The order of every product is the model's.

## Inputs
* `T` – Taylor model
* `k` – exponent

## Output
* Taylor model of the power
-/

-- Authors:       Claude Opus 5.5
-- Written:       20-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- The loop of binary exponentiation: while `k > 0`, the result times the base if `k` is odd, the
base squared if `k > 1`, and `k` halved; every product `Taylm.timesMerged` at the order `N`. The
first argument bounds the passes (`k` suffices). -/
@[step_of Taylm.powBinary]
def Taylm.step_powBinary (N : ℕ) : ℕ → Taylm 𝕋 n → Taylm 𝕋 n → ℕ → Taylm 𝕋 n
  | 0, R, _, _ => R
  | fuel + 1, R, B, k =>
    if k = 0 then R
    else
      -- the result takes the base for an odd `k`; the base is squared while bits remain
      let R' := if k % 2 = 1 then Taylm.timesMerged N R B else R
      let B' := if 1 < k then Taylm.timesMerged N B B else B
      Taylm.step_powBinary N fuel R' B' (k / 2)


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.powBinary (T : Taylm 𝕋 n) (k : ℕ) : Taylm 𝕋 n :=
  Taylm.step_powBinary T.maxOrder k (Taylm.const n one T.maxOrder) T k

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
