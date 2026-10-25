module

public import CORALean.Specification.STL.STL
public import CORALean.Specification.STL.Operations.Basic

@[expose] public section

/-!
# Finally in STL

`ξ ⊨ₜ F[a,b] φ` holds iff `φ` holds on the trace shifted by some `t ∈ [a,b]`: the clause of the
`until` of [1, Sec. 2.2] for `F[a,b] φ := true U[a,b] φ`, the always-true left operand dropped.

## Inputs
* `a` – interval lower bound
* `b` – interval upper bound
* `φ` – formula
* `ξ` – trace

## Hypotheses
* none

## Conclusion
* eventually holds iff the formula holds at some shifted time of the interval

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and Hybrid
      Systems". Automated Technology for Verification and Analysis, 2016.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {X : Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.Formula.sat_finally (a b : ℝ≥0) (φ : STL.Formula X) (ξ : ℝ≥0 → X) :
    (STL.Formula.finally a b φ).Satisfies ξ ↔
      ∃ t, a ≤ t ∧ t ≤ b ∧ φ.Satisfies (Time.shift ξ t) := by
  simp [STL.Formula.finally, STL.Formula.tt, STL.Formula.Satisfies]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
