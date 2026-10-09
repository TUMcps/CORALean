import CORALean.ContSet.ContSet.Definitions.HyperplanePolyhedron
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Mul

/-!
# A set lies in the polyhedron of its bounds

[1, Sec. 3.1]: if `m_ℓ ≤ x·ℓ ≤ M_ℓ` for every `x` in `X` and every `ℓ ∈ D`, in particular for
the infimum and the supremum of `{x·ℓ | x ∈ X}` (when those exist), then `X` lies in
`{x | ∀ ℓ ∈ D, m_ℓ ≤ x·ℓ ≤ M_ℓ}`. This is what makes the polyhedron an over-approximation.

## References

* [1] A. Girard and C. Le Guernic. "Zonotope/Hyperplane Intersection for Hybrid Systems
      Reachability Analysis". In Hybrid Systems: Computation and Control (HSCC), LNCS 4981,
      Springer, 2008, pp. 215-228.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 3.1]: valid bounds in the directions of `D` put `X` in their polyhedron. -/
theorem ContSet.subset_hyperplanePolyhedron {X : Set (Vec ℝ n)} {D : Finset (Vec ℝ n)}
    {m M : Vec ℝ n → ℝ} (hX : ∀ x ∈ X, ∀ ℓ ∈ D, m ℓ ≤ x ⬝ᵥ ℓ ∧ x ⬝ᵥ ℓ ≤ M ℓ) :
    X ⊆ ContSet.hyperplanePolyhedron D m M :=
  fun x hx ℓ hℓ => hX x hx ℓ hℓ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
