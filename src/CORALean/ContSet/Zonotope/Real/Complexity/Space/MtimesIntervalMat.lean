module

public import CORALean.ContSet.Zonotope.Real.Operations.MtimesIntervalMat

@[expose] public section

/-!
# `Zonotope.mtimesIntervalMat_h`

Multiplying by an interval matrix keeps the operand's generators and boxes the
radius into one fresh generator per output coordinate: `m` more, where `m` is
the row count of the matrix, not a function of the operand's own size. `rfl`,
since `Operations/MtimesIntervalMat.lean` states `h` directly.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.mtimesIntervalMat_h (IM : Interval (Mat ℝ m n)) (Z : Zonotope (Vec ℝ n)) :
    (Zonotope.mtimesIntervalMat IM Z).h = Z.h + m := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
