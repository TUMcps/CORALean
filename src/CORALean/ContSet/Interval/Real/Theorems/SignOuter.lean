module

public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.ContSet.Interval.Real.Theorems.MonotoneImageOuter
public import CORALean.ContSet.Interval.Real.Theorems.Basic

@[expose] public section

/-!
# `Interval.sign` contains the image under the sign

`sign` is monotone but not continuous, so the image of a box is not a box (the image of `[-1, 1]`
is `{-1, 0, 1}` and `[0, 1]` is the hull of `{0, 1}`): only the outer statement holds, with no
hypothesis.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.sign_outer (I : Interval (Vec ℝ n)) :
    (fun x i => Real.sign (x i)) '' I.construct ⊆ I.sign.construct :=
  Interval.monotoneImage_outer Real.sign sign_monotone I


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
