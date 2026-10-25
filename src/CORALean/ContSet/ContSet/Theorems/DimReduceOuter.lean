module

public import CORALean.ContSet.ContSet.Definitions.DimReduce
public import CORALean.ContSet.ContSet.Definitions.IsBoundIntersect2D
public import CORALean.ContSet.ContSet.Theorems.HyperplaneSliceEq
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# Dimension reduction over-approximates the hyperplane intersection

[1, Alg. 2]: with `BOUND_INTERSECT_2D` as specified, the polyhedron returned contains
`Z ∩ G`. A point `x ∈ Z` with `x·n = γ` has `(γ, x·ℓ) ∈ Π_{n,ℓ}(Z)` ([1, Prop. 1]), so `x·ℓ`
lies in the segment the routine returns for that plane set, for every `ℓ ∈ D`.

## Inputs
* `bound` – bound-intersect oracle
* `Z` – set
* `nv` – normal of the hyperplane
* `γ` – offset of the hyperplane
* `D` – directions

## Hypotheses
* `hb` – `bound` meets its specification

## Conclusion
* the intersection of `Z` with the hyperplane lies in the polyhedron

## References

* [1] A. Girard and C. Le Guernic. "Zonotope/Hyperplane Intersection for Hybrid Systems Reachability
      Analysis". Hybrid Systems: Computation and Control, 2008.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 2]: the polyhedron contains `Z ∩ G`, for any `bound` meeting its specification. -/
theorem ContSet.dimReduce_outer {bound : Set (ℝ × ℝ) → ℝ → Real.Interval ℝ}
    (hb : ContSet.IsBoundIntersect2D bound) (Z : Set (Vec ℝ n)) (nv : Vec ℝ n) (γ : ℝ)
    (D : Finset (Vec ℝ n)) : -- --- CONCL ---
    {x | x ∈ Z ∧ x ⬝ᵥ nv = γ} ⊆ ContSet.dimReduce bound Z nv γ D := by -- --- PROOF ---
  rintro x ⟨hx, hxn⟩ ℓ _
  -- the `y = x·ℓ` is in the slice of the projection, which is the segment `[m, M]`
  have hy : x ⬝ᵥ ℓ ∈ {y : ℝ | (γ, y) ∈ (fun x : Vec ℝ n => (x ⬝ᵥ nv, x ⬝ᵥ ℓ)) '' Z} := by
    rw [← ContSet.hyperplane_slice_eq]
    exact ⟨x, hx, hxn, rfl⟩
  rw [hb] at hy
  exact hy

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
