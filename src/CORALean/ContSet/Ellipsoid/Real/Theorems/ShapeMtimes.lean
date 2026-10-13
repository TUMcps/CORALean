module

public import CORALean.ContSet.Ellipsoid.Real.Operations.Mtimes
public import CORALean.ContSet.Ellipsoid.Real.Operations.Shape

@[expose] public section

/-!
# The shape matrix of a linear image

[1, Lemma 2]: `T E(E, ē) = E(T E Tᵀ, T ē)`. The set equality is `Ellipsoid.mtimes_exact` — exact
for any `T` in the generator form `ē + G B`, `E = G Gᵀ` — and this is the shape matrix:
`(T G)(T G)ᵀ = T (G Gᵀ) Tᵀ`.

## References

* [1] V. Gaßmann and M. Althoff. "Scalable Zonotope-Ellipsoid Conversions using the Euclidean
      Zonotope Norm". In Proc. of the 2020 American Control Conference (ACC), pp. 4715-4721,
      2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.shape_mtimes (M : Mat ℝ m n) (E : Ellipsoid n) :
    (Ellipsoid.mtimes M E).shape = M * E.shape * Mᵀ := by
  simp only [Ellipsoid.shape, Ellipsoid.mtimes, Matrix.transpose_mul, Matrix.mul_assoc]
  exact Matrix.mul_assoc _ _ _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
