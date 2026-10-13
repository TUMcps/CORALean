module

public import CORALean.ContSet.ContSet.Definitions.HyperplanePolyhedron
public import CORALean.Global.Tensor
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# Dimension reduction of a hyperplane intersection

[1, Alg. 2]: to over-approximate `Z ∩ G`, `G = {x | x·n = γ}`, in the directions of a finite
set `D`, project `Z` by `Π_{n,ℓ}(x) = (x·n, x·ℓ)` for each `ℓ ∈ D`, intersect the plane image
with the line `L_γ` by `BOUND_INTERSECT_2D` to get `[m_ℓ; M_ℓ]`, and return
`{x | ∀ ℓ ∈ D, m_ℓ ≤ x·ℓ ≤ M_ℓ}`. The intersection routine is an argument `bound`
(`IsBoundIntersect2D` is what it owes), as the optimizer is in `Zonotope.reduceCoOptSVD`.

## References

* [1] A. Girard and C. Le Guernic. "Zonotope/Hyperplane Intersection for Hybrid Systems
      Reachability Analysis". In Hybrid Systems: Computation and Control (HSCC), LNCS 4981,
      Springer, 2008, pp. 215-228.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 2]: the polyhedron of the bounds `bound` returns on each `Π_{n,ℓ}(Z)`. -/
def ContSet.dimReduce (bound : Set (ℝ × ℝ) → ℝ → ℝ × ℝ) (Z : Set (Vec ℝ n)) (nv : Vec ℝ n)
    (γ : ℝ) (D : Finset (Vec ℝ n)) : Set (Vec ℝ n) :=
  ContSet.hyperplanePolyhedron D
    (fun ℓ => (bound ((fun x : Vec ℝ n => (x ⬝ᵥ nv, x ⬝ᵥ ℓ)) '' Z) γ).1)
    (fun ℓ => (bound ((fun x : Vec ℝ n => (x ⬝ᵥ nv, x ⬝ᵥ ℓ)) '' Z) γ).2)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
