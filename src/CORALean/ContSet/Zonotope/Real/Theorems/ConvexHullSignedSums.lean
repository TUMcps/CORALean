module

public import CORALean.ContSet.Zonotope.Real.Operations.SignedSums
public import CORALean.ContSet.Zonotope.Real.Theorems.ConstructEqConvexHullCorner

@[expose] public section

/-!
# The zonotope is the convex hull of `Z±(R)`

[1, Prop. 6.1, Eq. 39]: `C(Z±(R)) = Z(R)`, the centred zonotope with generators `R` being the
convex hull of the images of the cube's vertices. With a centre `c`, translate both sides
(`Zonotope.construct_eq_convexHull_corner`).

## References

* [1] M. Maïga, N. Ramdani, L. Travé-Massuyès and C. Combastel. "A Comprehensive Method for
      Reachability Analysis of Uncertain Nonlinear Hybrid Systems". IEEE Transactions on
      Automatic Control, 61(9):2341-2356, 2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.convexHull_signedSums (R : Fin p → Vec ℝ n) :
    convexHull ℝ (Zonotope.signedSums R) =
      (⟨p, 0, R⟩ : Zonotope (Vec ℝ n)).construct := by -- --- PROOF ---
  rw [Zonotope.construct_eq_convexHull_corner]
  congr 1
  -- the corners are the signed sums, the centre being `0`
  ext x
  constructor
  · rintro ⟨σ, rfl⟩
    exact ⟨σ, by simp [Zonotope.corner]⟩
  · rintro ⟨σ, rfl⟩
    exact ⟨σ, by simp [Zonotope.corner]⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
