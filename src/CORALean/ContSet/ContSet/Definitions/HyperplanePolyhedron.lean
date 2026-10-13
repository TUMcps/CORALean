module

public import CORALean.Global.Tensor
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# The polyhedron cut out by bounds in finitely many directions

[1, Sec. 3.1]: a set `X` is bounded tightly by hyperplanes with normals in a finite set
`D = {ℓ₁, …, ℓ_p}`: with `m_ℓ` and `M_ℓ` the infimum and supremum of `{x·ℓ | x ∈ X}`, the
over-approximation is `P = {x | ∀ ℓ ∈ D, m_ℓ ≤ x·ℓ ≤ M_ℓ}`. The bounds are arguments, so the
same set serves for the exact infimum and supremum and for any enclosing pair.

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

/-- [1, Sec. 3.1]: `{x | ∀ ℓ ∈ D, m ℓ ≤ x·ℓ ≤ M ℓ}`. -/
def ContSet.hyperplanePolyhedron (D : Finset (Vec ℝ n)) (m M : Vec ℝ n → ℝ) :
    Set (Vec ℝ n) :=
  {x | ∀ ℓ ∈ D, m ℓ ≤ x ⬝ᵥ ℓ ∧ x ⬝ᵥ ℓ ≤ M ℓ}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
