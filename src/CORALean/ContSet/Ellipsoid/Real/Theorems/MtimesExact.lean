import CORALean.ContSet.Ellipsoid.Real.Operations.Mtimes

/-!
# A linear image of an ellipsoid is exactly an ellipsoid

The same unit-ball point works in both directions — a matrix in front of `G`
introduces no freedom and removes none — so associativity of `M (G u)` is the
whole proof. Exact for every `M`, singular ones included, where the shape-matrix
form would have had to take a square root of `M Q Mᵀ` to say the same thing.

In the shape-matrix form this is [1, Lemma 2], `T E(E, ē) = E(T E Tᵀ, T ē)`;
`Ellipsoid.shape_mtimes` is the shape.

## References

* [1] V. Gaßmann and M. Althoff. "Scalable Zonotope-Ellipsoid Conversions using the Euclidean
      Zonotope Norm". In Proc. of the 2020 American Control Conference (ACC), pp. 4715-4721,
      2020.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.mtimes_exact (M : Mat ℝ m n) (E : Ellipsoid n) :
    (M *ᵥ ·) '' E.construct = (Ellipsoid.mtimes M E).construct := by -- --- PROOF ---
  have haff : ∀ u : Vec ℝ E.k, M *ᵥ (E.q + E.G *ᵥ u)
      = (Ellipsoid.mtimes M E).q + (Ellipsoid.mtimes M E).G *ᵥ u := fun u => by
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec]
    rfl
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨u, hu, haff u⟩
  · rintro y ⟨u, hu, hy⟩
    exact ⟨E.q + E.G *ᵥ u, ⟨u, hu, rfl⟩, (haff u).trans hy.symm⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
