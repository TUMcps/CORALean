import CORALean.ContSet.Interval.Float.Theorems.HalveMinusMem
import CORALean.ContSet.Interval.Float.Theorems.MtimesMem
import CORALean.NN.Theorems.ToRealMatMapAbsolute
import CORALean.NN.Operations.IntervalChainFwdFloat

/-!
# The linear layer's radius is in its float box
The radius `r = |W| (u - l)/2` of the layer's output interval, for `l`, `u` in their boxes, is in
the box `IntervalChainFloat.fwd` and `backprop` compute it as.
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

theorem IntervalChainFloat.linear_r_mem {n m : ℕ} (W : Mat 𝕋 m n)
    {P : Interval (Vec 𝕋 n) × Interval (Vec 𝕋 n)} {p : Vec ℝ n × Vec ℝ n}
    (h1 : p.1 ∈ P.1.construct) (h2 : p.2 ∈ P.2.construct) :
    (toRealMat W).map abs *ᵥ ((1 / 2 : ℝ) • (p.2 - p.1))
      ∈ (Interval.mtimes (W.map absolute)
          (Interval.halve (Interval.minus P.2 P.1))).construct :=
  Interval.mtimes_mem _ _ (toRealMat_map_absolute W) _ (Interval.halve_minus_mem h2 h1)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
