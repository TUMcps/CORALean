module

public import CORALean.Specification.STL.STL

@[expose] public section

/-!
# Negation in STL

`ξ ⊨ₜ ¬φ ⇔ ξ ⊭ₜ φ`, the negation clause of [1, Sec. 2.2]. CORA's `not` builds a syntax-tree node
and evaluates nothing, so this is the semantics the node is read with.

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

theorem STL.Formula.sat_not (φ : STL.Formula X) (ξ : ℝ≥0 → X) :
    (STL.Formula.not φ).Sat ξ ↔ ¬ φ.Sat ξ := Iff.rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
