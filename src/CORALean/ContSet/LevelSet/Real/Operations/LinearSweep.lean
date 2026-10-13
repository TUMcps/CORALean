import CORALean.ContSet.LevelSet.Real.Operations.LinearCoord
import CORALean.ContSet.Interval.Real.Operations.Center

/-!
# `LevelSet.linearSweep`

One pass of the loop of `aux_contractorLinear` in CORA's `@levelSet/tightenDomain`: the centre `m`
of the box, the interval gradient `k` on it and the value `f(m)` are computed once, then the
coordinates are tightened in turn, each seeing the box the earlier ones have narrowed.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def LevelSet.linearSweep (f : Vec ℝ n → ℝ)
    (grad : Interval (Vec ℝ n) → Interval (Vec ℝ n)) (int : Interval (Vec ℝ n)) :
    Interval (Vec ℝ n) :=
  let m := int.center             -- m = center(int)
  let k := grad int               -- k = obj.der.grad(int)
  let fm := f m                   -- f = obj.funHan(m)
  (List.finRange n).foldl (fun X j => LevelSet.linearCoord fm m k j X) int

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
