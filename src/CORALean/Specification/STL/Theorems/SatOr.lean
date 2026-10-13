import CORALean.Specification.STL.STL

/-!
# Disjunction in STL

`ξ ⊨ₜ φ ∨ ψ ⇔ ξ ⊨ₜ φ ∨ ξ ⊨ₜ ψ`, [1, Sec. 2.2]'s clause for `∨`, as a rewrite that leaves the
semantics of the operands folded.

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

theorem STL.Formula.sat_or (φ ψ : STL.Formula X) (ξ : ℝ≥0 → X) :
    (STL.Formula.or φ ψ).Sat ξ ↔ φ.Sat ξ ∨ ψ.Sat ξ :=
  Iff.rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
