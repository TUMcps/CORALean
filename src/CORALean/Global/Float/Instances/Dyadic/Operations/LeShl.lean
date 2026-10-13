import CORALean.Global.Float.Instances.Dyadic.Dyadic

/-!
# `m ≤ n * 2 ^ g` without the power

For `n ≠ 0` and `g` above the bit length of `m`, `|n| * 2 ^ g` exceeds `|m|` and only the sign of
`n` decides, so the power is formed only when `g` is at most the bit length of `m`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

namespace Dyadic

variable {p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def leShl (m n : ℤ) (g : ℕ) : Bool :=
  if n = 0 then decide (m ≤ 0)
  else if Nat.log2 m.natAbs < g then decide (0 < n)
  else decide (m ≤ n * 2 ^ g)

end Dyadic

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
