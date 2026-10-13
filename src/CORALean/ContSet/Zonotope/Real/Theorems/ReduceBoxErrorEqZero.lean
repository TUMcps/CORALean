import CORALean.ContSet.Zonotope.Real.Operations.ReduceBoxError
import CORALean.ContSet.Zonotope.Real.Operations.AdaptSetOrderLoop
import CORALean.ContSet.Zonotope.Real.Operations.AdaptSetOrder

/-!
# An order that drops no generator costs nothing

`Zonotope.reduceBoxError Z o` is `err(·)` of the box a reduction to order `o` absorbs
the generators it drops into, so it reads `0` as soon as `o` is coarse enough to drop
none: `reduceBox` is the origin there, whose box reaches `0` from the origin.

Both adaptive order searches in this tree start from that fact. [1, Alg. 3] descends
from an order it already knows admissible, and TAC'23's `Alg. 2` (lines 19-22) sweeps
*upward* and needs somewhere for the sweep to land — which is why this is a file of its
own rather than a helper beside either.

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
-/

-- Authors:       Claude Opus 5
-- Written:       19-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- An order large enough to drop nothing costs nothing: `reduceBox` is the
origin there, whose box reaches `0` from the origin. -/
theorem Zonotope.reduceBoxError_eq_zero (Z : Zonotope (Vec ℝ n)) {o : ℕ} (h : Z.h ≤ o * n) :
    Z.reduceBoxError o = 0 := by -- --- PROOF ---
  have hbox : Z.reduceBox o = Zonotope.ofPoint 0 := by
    rw [Zonotope.reduceBox, dif_neg (Nat.not_lt.mpr h)]
  have hzero : (fun j => (Zonotope.ofPoint (0 : Vec ℝ n)).absBound j) = (0 : Vec ℝ n) := by
    funext j
    simp [Zonotope.absBound, Zonotope.ofPoint]
  rw [Zonotope.reduceBoxError, hbox, hzero, norm₂_zero]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
