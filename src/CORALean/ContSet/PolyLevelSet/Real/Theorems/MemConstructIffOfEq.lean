module

public import CORALean.ContSet.PolyLevelSet.Real.PolyLevelSet

@[expose] public section

/-!
# A polynomial level set of equations

Where every row is `=`, a point is in the set exactly when it solves `A μ_R(x) = b` row by row:
the form [1, Def. 5] writes a constrained polynomial zonotope's constraint in.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- With `=` in every row, membership is the system of equations `A μ_R(x) = b`. -/
theorem PolyLevelSet.mem_construct_iff_of_eq {P : PolyLevelSet n} (h : ∀ i, P.op i = .eq)
    {x : Vec ℝ n} :
    x ∈ P.construct ↔ ∀ i, (P.A *ᵥ PolyZonotope.monomial P.R x) i = P.b i := by
  refine forall_congr' fun i => ?_
  rw [h i]
  exact sub_eq_zero (a := (P.A *ᵥ PolyZonotope.monomial P.R x) i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
