module

public import Mathlib.Analysis.InnerProductSpace.Basic

@[expose] public section

/-!
# The billiard reflection

`[1, Alg., step 3]`: at a boundary point with unit internal normal `s` the direction changes as
`d → d - 2 (d, s) s`. Written over any real inner product space, which is what lets the same
line serve a polytope in `ℝⁿ` and, with the trace inner product, the matrix case of
`[1, Sec. 2.3]`, `D → D - 2 trace(DS) S`. A reflection only when `‖s‖ = 1`, as the paper says
`‖s‖ = 1`; `BilliardReflectLaw.lean` is that law.

## References

* [1] B. T. Polyak and E. N. Gryazina. "Billiard walk - a new sampling algorithm for control
      and optimization". In Proc. of the 19th IFAC World Congress, Cape Town, South Africa,
      IFAC Proceedings Volumes 47(3), pp. 6123-6128, 2014.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `d - 2 (d, s) s`, `[1, Alg., step 3]`. -/
def billiardReflect (s d : E) : E :=
  d - (2 * inner ℝ d s) • s

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
