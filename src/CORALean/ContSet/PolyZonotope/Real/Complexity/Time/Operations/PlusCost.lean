module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Plus
public import CORALean.Global.Cost

@[expose] public section

/-!
# `PolyZonotope.plusCost`

Asserted, not proved: `Operations/Plus.lean` adds the two centers — `n`
additions at `Vec ℝ n` — and concatenates all three generator blocks, which is
index work and free under `Global/Cost.lean`'s model.

`plusE` is free for the same reason. It lays the two exponent matrices out
block-diagonally, and every entry it produces is either one the operand already
held or the literal `0`; nothing is computed, so neither the factor counts nor
the generator counts enter. That the *result* carries `p₁ + p₂` factors is a
size claim and lives in `Complexity/Space/Theorems/PlusP.lean`, where it is proved.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `PolyZonotope.plus` costs at `Vec ℝ n`: `n` additions for the center,
and nothing for the three concatenations or for the exponent matrix. -/
def PolyZonotope.plusCost (n : ℕ) : Cost := ⟨n⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
