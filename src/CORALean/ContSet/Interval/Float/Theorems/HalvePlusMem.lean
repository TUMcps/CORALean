import CORALean.ContSet.Interval.Float.Theorems.HalveOuter
import CORALean.ContSet.Interval.Float.Theorems.PlusOuter

/-!
# Half a sum of two vectors in boxes is in the halved sum box
The sum is in the `Interval.plus` box, and `Interval.halve` is exact.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.halve_plus_mem {n : ℕ} {P Q : Interval (Vec 𝕋 n)} {x y : Vec ℝ n}
    (hx : x ∈ P.construct) (hy : y ∈ Q.construct) :
    (1 / 2 : ℝ) • (x + y) ∈ (Interval.halve (Interval.plus P Q)).construct :=
  Interval.halve_outer (Interval.plus_outer P Q (Set.add_mem_add hx hy))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
