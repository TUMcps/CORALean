import CORALean.ContSet.PolyZonotope.Real.Operations.MtimesIntervalMat

/-!
# `PolyZonotope.mtimesIntervalMat`'s counts

Multiplying by an interval matrix keeps the dependent factors and generators
and boxes the radius into one fresh *independent* generator per output
coordinate: `m` more, the matrix's row count, unrelated to the operand's own
size. `rfl` against the structure instance in `Operations/MtimesIntervalMat.lean`.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.mtimesIntervalMat_p (IM : Interval (Mat ℝ m n))
    (pZ : PolyZonotope (Vec ℝ n)) : (PolyZonotope.mtimesIntervalMat IM pZ).p = pZ.p := rfl

theorem PolyZonotope.mtimesIntervalMat_h (IM : Interval (Mat ℝ m n))
    (pZ : PolyZonotope (Vec ℝ n)) : (PolyZonotope.mtimesIntervalMat IM pZ).h = pZ.h := rfl

theorem PolyZonotope.mtimesIntervalMat_q (IM : Interval (Mat ℝ m n))
    (pZ : PolyZonotope (Vec ℝ n)) : (PolyZonotope.mtimesIntervalMat IM pZ).q = pZ.q + m := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
