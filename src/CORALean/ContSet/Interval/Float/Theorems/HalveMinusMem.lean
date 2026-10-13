import CORALean.ContSet.Interval.Float.Theorems.HalveOuter
import CORALean.ContSet.Interval.Float.Theorems.MinusOuter

/-!
# Half a difference of two vectors in boxes is in the halved difference box
The difference is in the `Interval.minus` box, and `Interval.halve` is exact.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.halve_minus_mem {n : ℕ} {P Q : Interval (Vec 𝕋 n)} {x y : Vec ℝ n}
    (hx : x ∈ P.construct) (hy : y ∈ Q.construct) :
    (1 / 2 : ℝ) • (x - y) ∈ (Interval.halve (Interval.minus P Q)).construct :=
  Interval.halve_outer (Interval.minus_outer P Q (Set.sub_mem_sub hx hy))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
