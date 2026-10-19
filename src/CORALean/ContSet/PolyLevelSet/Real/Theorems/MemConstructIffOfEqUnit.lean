module

public import CORALean.ContSet.Interval.Real.Theorems.Basic
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.MemConstructIffOfEq

@[expose] public section

/-!
# A polynomial level set of equations on the unit box

Where every row is `=` and the box is `[-1, 1]ⁿ`, a point is in the set exactly when every
coordinate has modulus at most `1` and it solves `A μ_R(x) = b`: [1, Def. 7]'s `constrDom`, the
factors of a constrained polynomial zonotope.

## Inputs
* `P` – polynomial level set
* `x` – point

## Hypotheses
* `h` – all rows are equations
* `hD` – box is the unit box

## Conclusion
* `x` lies in the set iff it is in the unit box and solves each row

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Equations on the unit box: a point is in the cube and solves `A μ_R(x) = b`. -/
theorem PolyLevelSet.mem_construct_iff_of_eq_unit {P : PolyLevelSet n} (h : ∀ i, P.op i = .eq)
    (hD : P.dom = Interval.unit n) {x : Vec ℝ n} : x ∈ P.construct
      ↔ (∀ k, |x k| ≤ 1) ∧ ∀ i, (P.A *ᵥ PolyZonotope.monomial P.R x) i = P.b i := by
  rw [PolyLevelSet.mem_construct_iff_of_eq h, hD, Interval.mem_unit_iff]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
