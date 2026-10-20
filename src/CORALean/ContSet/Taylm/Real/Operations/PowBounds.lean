module

public import Mathlib.Data.Real.Basic
public import CORALean.ContSet.Interval.Real.Interval

@[expose] public section

/-!
# `[l, u]ᵏ`

The power of an interval in interval arithmetic: `[1, 1]` at `k = 0`, for odd `k` the image of
the monotone `xᵏ`, for even `k` from `0` (when the interval holds it) or the smaller end's power
to the larger one's. The building block of [1, Eq. 12].

## Inputs
* `l` – lower end
* `u` – upper end
* `k` – exponent

## Output
* range of the power over the interval

## References

* [1] M. Althoff, D. Grebenyuk, and N. Kochdumper. "Implementation of Taylor Models in CORA
      2018". In Proc. of the 5th International Workshop on Applied Verification of Continuous
      and Hybrid Systems (ARCH18), EPiC Series in Computing, vol. 54, pp. 145-173, 2018.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.powBounds (l u : ℝ) (k : ℕ) : Interval ℝ :=
  if k = 0 then ⟨1, 1⟩
  else if Even k then ⟨if l ≤ 0 ∧ 0 ≤ u then 0 else min (l ^ k) (u ^ k), max (l ^ k) (u ^ k)⟩
  else ⟨l ^ k, u ^ k⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
