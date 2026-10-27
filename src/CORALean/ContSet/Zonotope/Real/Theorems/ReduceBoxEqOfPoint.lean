module

public import CORALean.ContSet.Zonotope.Real.Operations.ReduceBox

@[expose] public section

/-!
# `reduceBox` vanishes exactly, not merely in the limit

`reduceBox`'s own `dite` already says this: past the order that drops no generator, the box is
`ofPoint 0` outright, no sequence or limit needed. What this theorem adds is the closed form of
that threshold, `Z.h ≤ o * n`, read off `reduceBox_h` rather than assumed — the one
`Zonotope.reduce` itself leaves alone. `[1]` tunes the zonotope order against an error the caller
states; this makes the order side of that tuning *attained* rather than approached, unlike
`MatExp.expRemainderOrder`'s `ε`, whose bound only tends to `0`.

## Inputs
* `Z` – zonotope
* `o` – target order

## Hypotheses
* `h` – order drops no generator

## Conclusion
* the box is the origin

## References

* [1] [M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning for reachability
      analysis of linear systems". 2020 59th IEEE Conference on Decision and Control (CDC),
      2020.](../../../../../../references/2020/wetzlinger-cdc-adaptive-tuning.md)
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Once the order drops no generator, the box is the origin, exactly. -/
theorem Zonotope.reduceBox_eq_ofPoint {Z : Zonotope (Vec ℝ n)} {o : ℕ} (h : Z.h ≤ o * n) :
    Z.reduceBox o = Zonotope.ofPoint 0 := by
  unfold Zonotope.reduceBox
  rw [dif_neg (not_lt.mpr h)]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
