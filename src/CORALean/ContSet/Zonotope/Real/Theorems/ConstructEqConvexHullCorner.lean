module

public import CORALean.ContSet.Conversion.Real.Zonotope_to_VPolytope

@[expose] public section

/-!
# A zonotope is the convex hull of its sign corners

`vPolytope_exact` read without the `VPolytope`: the corners `c + ∑ ±gⱼ`, indexed by sign
vectors rather than by `Fin (2 ^ h)`. What every vertex-enumeration argument starts from: a
convex function attains its maximum over the zonotope at a corner, which is why
`[1, Alg. 1]` need only test the corners.

## References

* [1] A. Kulmburg and M. Althoff. "On the co-NP-Completeness of the Zonotope Containment
      Problem". European Journal of Control, 62:84-91, 2021.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.construct_eq_convexHull_corner (Z : Zonotope α) :
    Z.construct = convexHull ℝ (Set.range Z.corner) := by -- --- PROOF ---
  rw [← Z.vPolytope_exact, VPolytope.construct_eq_convexHull]
  congr 1
  -- the corners indexed by `Fin (2 ^ h)` are the corners indexed by sign vectors
  ext x
  constructor
  · rintro ⟨l, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨σ, rfl⟩
    exact ⟨(signEquiv Z.h).symm σ, by simp [Zonotope.vPolytope]⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
