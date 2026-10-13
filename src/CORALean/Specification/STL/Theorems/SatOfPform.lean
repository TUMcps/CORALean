import CORALean.Specification.STL.STL

/-!
# A non-temporal formula in STL

`ξ ⊨ₜ ϱ ⇔ ξ(0) ⊨ₚ ϱ`, which is how [1, Eq. 10]'s proof reads a non-temporal formula.

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". ATVA, LNCS 9938, pp. 412-427, 2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {X : Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.Formula.sat_ofPform (ϱ : Pform X) (ξ : ℝ≥0 → X) :
    (STL.Formula.ofPform ϱ).Sat ξ ↔ ϱ.Sat (ξ 0) := by
  induction ϱ with
  | atom p => rfl
  | not ϱ ih => exact not_congr ih
  | or ϱ₁ ϱ₂ ih₁ ih₂ => exact or_congr ih₁ ih₂

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
