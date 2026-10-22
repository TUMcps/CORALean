module

public import CORALean.ContSet.Zonotope.Float.Operations.ErrOp
public import CORALean.ContSet.Zonotope.Float.Operations.ReduceGirardBox
public import CORALean.Global.Float.Interfaces
public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# `Alg. 3` lines 3-7 in floats: the order-decrementing loop

[1, Alg. 3]'s `Real.Zonotope.adaptSetOrderLoop` computed in `𝕋`: decrement the order while
the box a reduction one order down absorbs, measured by `errOp`, still clears
the share `εSi`, and keep the last order that did. The comparison is in ℚ,
through `ToRat`, so it is exact; the measure is the sup-norm `errOp`.

A NaN `errOp` reads through `ToRat` as `1.5 · 2 ^ 1024`, fails `≤ εSi` and keeps the higher
order. Tightness only: every order is a `reduce`.

## Inputs
* `Z` – zonotope to reduce
* `εSi` – admissible error share

## Output
* order kept by lines 3 to 7

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lines 3-7: decrement the order while the reduction one order down still
clears the share, and keep the last order that did. -/
def Zonotope.adaptSetOrderLoop (Z : Zonotope (Vec 𝕋 n)) (εSi : ℚ) : ℕ → ℕ → ℕ
  | Φset, 0 => Φset
  | 0, _ + 1 => 0
  | Φset + 1, k + 1 =>
    if ToRat.toRat (Z.reduceGirardBox Φset).errOp ≤ εSi then Z.adaptSetOrderLoop εSi Φset k
    else Φset + 1

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
