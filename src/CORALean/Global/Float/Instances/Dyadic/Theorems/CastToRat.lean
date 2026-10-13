module

public import CORALean.Global.Float.Instances.Dyadic.Operations.ToRat

@[expose] public section

/-!
# `Dyadic.toRat` is the number `toReal` reads

`toReal` already takes its power of two through ℚ, so the two agree by casting
the product: nothing is rounded on either side.
-/

-- Authors:       Claude Opus 5.5
-- Written:       30-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float


-- =======================================  MAIN THEOREM  ======================================= --

theorem Dyadic.cast_toRat {p : ℕ} (d : Dyadic p) :
    ((d.toRat : ℚ) : ℝ) = d.toReal := by
  rw [Dyadic.toRat, Dyadic.toReal, Rat.cast_mul, Rat.cast_intCast]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
