module

public import CORALean.ContSet.ConZonotope.Real.Operations.TightenCoeff

@[expose] public section

/-!
# `ConZonotope.tightenRow`

[1, Alg. 1], [2, Alg. 1], lines 2, 6-8: the inner loop over columns, for row `i` fixed — every
coefficient met in turn with row `i`'s own bound.

## References

* [1] V. Raghuraman and J. P. Koeln. "Set operations and order reductions for
      constrained zonotopes". Automatica, 139:110204, 2022. arXiv:2009.06039.
* [2] J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes:
      A new tool for set-based estimation and fault detection". Automatica, 69:126-136,
      2016.
-/

-- Authors:       Claude Opus 5
-- Written:       21-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lines 2, 6-8: the inner loop over columns, for row `i` fixed. -/
noncomputable def ConZonotope.tightenRow {nc ng : ℕ} (A : Mat ℝ nc ng) (b : Vec ℝ nc)
    (i : Fin nc) (E : Interval (Vec ℝ ng)) : Interval (Vec ℝ ng) :=
  Fin.foldl ng (fun E j => ConZonotope.tightenCoeff A b i j E) E

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
