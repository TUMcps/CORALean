module

public import CORALean.Specification.STL.STL
public import CORALean.Specification.STL.Operations.Basic

@[expose] public section

/-!
# Globally in STL

`ξ ⊨ₜ G[a,b] φ` holds iff `φ` holds on the trace shifted by every `t ∈ [a,b]`: the dual `¬F[a,b]
¬φ` of the eventuality `F[a,b]` of [1, Sec. 2.2] (the paper does not define `G`).

## Inputs
* `a` – interval lower bound
* `b` – interval upper bound
* `φ` – formula
* `ξ` – trace

## Hypotheses
* none

## Conclusion
* always holds iff the formula holds at every shifted time of the interval

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". ATVA, LNCS 9938, pp. 412-427, 2016.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {X : Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.Formula.sat_globally (a b : ℝ≥0) (φ : STL.Formula X) (ξ : ℝ≥0 → X) :
    (STL.Formula.globally a b φ).Sat ξ ↔
      ∀ t, a ≤ t → t ≤ b → φ.Sat (Time.shift ξ t) := by
  simp only [STL.Formula.globally, STL.Formula.finally, STL.Formula.tt, STL.Formula.Sat]
  push Not
  exact forall_congr' fun t => by tauto

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
