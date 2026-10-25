module

public import CORALean.Specification.STL.STL

@[expose] public section

/-!
# Until in STL

`ξ ⊨ₜ φ U[a,b] ψ` holds iff `ψ` holds on the trace shifted by some `t ∈ [a,b]` and `φ` on every
shift strictly before `t`: [1, Sec. 2.2] as `Satisfies` states it. CORA's `until` builds a
syntax-tree node, and its `modelCheckTrace` reads it with `φ` required strictly before `t`.

## Inputs
* `a` – interval lower bound
* `b` – interval upper bound
* `φ` – holding formula
* `ψ` – target formula
* `ξ` – trace

## Hypotheses
* none

## Conclusion
* the until holds iff the target holds at a time of the interval after the other

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". ATVA, LNCS 9938, pp. 412-427, 2016.
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

theorem STL.Formula.sat_until (a b : ℝ≥0) (φ ψ : STL.Formula X) (ξ : ℝ≥0 → X) :
    (STL.Formula.until a b φ ψ).Satisfies ξ ↔ ∃ t, a ≤ t ∧ t ≤ b ∧ ψ.Satisfies (Time.shift ξ t) ∧
      ∀ t' < t, φ.Satisfies (Time.shift ξ t') := Iff.rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
