module

public import CORALean.ContSet.Zonotope.Real.Operations.NormUb
public import CORALean.ContSet.Interval.Real.Theorems.NormLe

@[expose] public section

/-!
# `Zonotope.normUb` bounds every member

The box contains the zonotope (`interval_contains`) and `Interval.norm` bounds the box.
An upper bound only, and not tight in general: a box is larger than its zonotope.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.norm₂_le_normUb {Z : Zonotope (Vec ℝ n)} {x : Vec ℝ n}
    (hx : x ∈ Z.construct) : ‖x‖₂ ≤ Z.normUb :=
  Interval.norm_le (Z.interval_contains hx)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
