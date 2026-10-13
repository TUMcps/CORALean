import CORALean.ContSet.Capsule.Float.Capsule

/-!
# `Capsule.isFullDim`, over a floating-point scalar

The characterisation of the exact layer (`Capsule.isFullDim_iff`), not CORA's `r > 0`, which
misses two thin cases: `0 < r`, or `0 ≤ r` and (`n = 0`, or `n = 1` with `g ≠ 0`). Every strict
inequality is certified by `ltStrict` and every weak one by `le`, so `true` is a proof and `false`
refutes nothing; `g ≠ 0` is a coordinate whose absolute value is certified positive.
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

def Capsule.isFullDim (C : Capsule 𝕋 n) : Bool :=
  ltStrict zero C.r ||
    (le zero C.r && (decide (n = 0) ||
      (decide (n = 1) && (List.finRange n).any fun j => ltStrict zero (absolute (C.g j)))))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
