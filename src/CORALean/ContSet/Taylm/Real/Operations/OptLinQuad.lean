import CORALean.ContSet.Taylm.Real.Operations.CosyGo
import CORALean.ContSet.Taylm.Real.Operations.Uminus

/-!
# `Taylm.optLinQuad`

CORA's `optLinQuad`: the bounds of a model over the normalized box by the LDB/QFB optimizer of
[1, Sec. 4], the lower end that of the minimum of `T`, the upper end minus that of `-T`. CORA's
optimizer reduces the domain by LDB before each bisection and seeds the QFB point by a gradient
search; this one bisects and takes the box's centre.

## References

* [1] K. Makino and M. Berz. "Verified Global Optimization with Taylor Model-based Range
      Bounders". Transactions on Computers, 11(4):1611-1618, 2005.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.optLinQuad (T : Taylm n) (ε : ℝ) (ldbFuel fuel : ℕ) : ℝ × ℝ :=
  ((T.cosyGo (fun _ => (-1, 1)) ε ldbFuel fuel).1,
    -(T.uminus.cosyGo (fun _ => (-1, 1)) ε ldbFuel fuel).1)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
