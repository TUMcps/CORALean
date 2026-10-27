module

public import CORALean.Global.Tensor
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# The slice of a set by a hyperplane is a slice of its plane projection

[1, Prop. 1]: for any set `Z`, hyperplane `G = {x | x·n = γ}` and vector `ℓ`,
`{x·ℓ | x ∈ Z ∩ G} = {y | (γ, y) ∈ Π_{n,ℓ}(Z)}` for `Π_{n,ℓ}(x) = (x·n, x·ℓ)`. Both sides
are the `y` reached by a point of `Z` whose first coordinate is `γ`. It reduces the
`d`-dimensional intersection to a line meeting a plane set, and holds for an arbitrary
set, not only a zonotope.

## Inputs
* `Z` – set
* `nv` – normal of the hyperplane
* `ℓ` – direction
* `γ` – offset of the hyperplane

## Hypotheses
* none

## Conclusion
* projections on `ℓ` of the slice equal the slice of the 2D projection

## References

* [1] [A. Girard and C. Le Guernic. "Zonotope/Hyperplane Intersection for Hybrid Systems
      Reachability Analysis". Hybrid Systems: Computation and Control,
      2008.](../../../../../references/2008/girard-hscc-zonotope-hyperplane.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 1]: `{x·ℓ | x ∈ Z ∩ G} = {y | (γ, y) ∈ Π_{n,ℓ}(Z)}`. -/
theorem ContSet.hyperplane_slice_eq (Z : Set (Vec ℝ n)) (nv ℓ : Vec ℝ n) (γ : ℝ) :
    {y : ℝ | ∃ x ∈ Z, x ⬝ᵥ nv = γ ∧ x ⬝ᵥ ℓ = y}
      = {y : ℝ | (γ, y) ∈ (fun x : Vec ℝ n => (x ⬝ᵥ nv, x ⬝ᵥ ℓ)) '' Z} := by
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_image, Prod.mk.injEq]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
