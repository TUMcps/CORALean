module

public import CORALean.ContSet.ContSet.Definitions.HyperplanePolyhedron
public import CORALean.ContSet.Interval.Real.Interval

@[expose] public section

/-!
# Dimension reduction of a hyperplane intersection

[1, Alg. 2]: to over-approximate `Z ∩ G`, `G = {x | x·n = γ}`, in the directions of a finite
set `D`, project `Z` by `Π_{n,ℓ}(x) = (x·n, x·ℓ)` for each `ℓ ∈ D`, intersect the plane image
with the line `L_γ` by `BOUND_INTERSECT_2D` to get `[m_ℓ; M_ℓ]`, and return
`{x | ∀ ℓ ∈ D, m_ℓ ≤ x·ℓ ≤ M_ℓ}`. The intersection routine is an argument `bound`
(`IsBoundIntersect2D` is what it owes), as the optimizer is in `Zonotope.reduceCoOptSVD`.

## Inputs
* `bound` – bound-intersect oracle
* `Z` – set
* `nv` – normal of the hyperplane
* `γ` – offset of the hyperplane
* `D` – directions

## Output
* polyhedron bounding `Z` intersected with the hyperplane

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


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 2]: the polyhedron of the bounds `bound` returns on each `Π_{n,ℓ}(Z)`. Line 5 is the
step numbered 3 here, since lines 1-4 are one loop. -/
def ContSet.dimReduce (bound : Set (ℝ × ℝ) → ℝ → Real.Interval ℝ) (Z : Set (Vec ℝ n)) (nv : Vec ℝ n)
    (γ : ℝ) (D : Finset (Vec ℝ n)) : Set (Vec ℝ n) :=
  -- 1. for every `ℓ ∈ D` (lines 1-4), the plane image of `Z` under `Π_{n,ℓ}(x) = (x·n, x·ℓ)`
  let Sπ := fun ℓ : Vec ℝ n => (fun x : Vec ℝ n => (x ⬝ᵥ nv, x ⬝ᵥ ℓ)) '' Z
  -- 2. its cut with the line `L_γ`, `[m_ℓ; M_ℓ] ← BOUND_INTERSECT_2D(Sπ_{n,ℓ}, L_γ)`
  let m := fun ℓ => (bound (Sπ ℓ) γ).inf
  let M := fun ℓ => (bound (Sπ ℓ) γ).sup
  -- 3. return `{x | ∀ ℓ ∈ D, m_ℓ ≤ x·ℓ ≤ M_ℓ}`
  ContSet.hyperplanePolyhedron D m M

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
