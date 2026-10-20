module

public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.ContSet.Interval.Float.Theorems.MtimesMem
public import CORALean.NN.Theorems.Basic
public import CORALean.NN.Operations.IntervalChainFwdFloat

@[expose] public section

/-!
# The linear layer's radius is in its float box
The radius `r = |W| (u - l)/2` of the layer's output interval, for `l`, `u` in their boxes, is in
the box `IntervalChain.fwd` and `backprop` compute it as.

## Inputs
* `n` – input width
* `m` – output width
* `W` – weight matrix
* `P` – boxes of the lower and upper input
* `p` – lower and upper input

## Hypotheses
* `h1` – the lower input lies in its box
* `h2` – the upper input lies in its box

## Conclusion
* the layer's radius lies in the float box
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

theorem IntervalChain.linear_r_mem {n m : ℕ} (W : Mat 𝕋 m n)
    {P : Interval (Vec 𝕋 n) × Interval (Vec 𝕋 n)} {p : Vec ℝ n × Vec ℝ n}
    (h1 : p.1 ∈ P.1.construct) (h2 : p.2 ∈ P.2.construct) :
    (toRealMat W).map abs *ᵥ ((1 / 2 : ℝ) • (p.2 - p.1))
      ∈ (Interval.mtimes (W.map absolute)
          (Interval.halve (Interval.minus P.2 P.1))).construct :=
  Interval.mtimes_mem _ _ (toRealMat_map_absolute W) _ (Interval.halve_minus_mem h2 h1)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
