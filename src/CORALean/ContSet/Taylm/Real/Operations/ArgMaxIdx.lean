module

public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# The index of the largest entry

The first index at which a list of reals is largest, `0` for the empty list: the `argmax` of
[1, Alg. 1], lines 8 and 9 (the latter on the negated lower bounds).

## Inputs
* `v` – list of reals

## Output
* index of the largest entry

## References

* [1] M. Althoff, D. Grebenyuk, and N. Kochdumper. "Implementation of Taylor Models in CORA
      2018". In Proc. of the 5th International Workshop on Applied Verification of Continuous
      and Hybrid Systems (ARCH18), EPiC Series in Computing, vol. 54, pp. 145-173, 2018.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.argMaxIdx (v : List ℝ) : ℕ :=
  (List.range v.length).foldl (fun best i => if v.getD best 0 < v.getD i 0 then i else best) 0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
