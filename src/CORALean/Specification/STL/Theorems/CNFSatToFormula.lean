import CORALean.Specification.STL.Operations.CNFToFormula
import CORALean.Specification.STL.Definitions.BranchHolds
import CORALean.Specification.STL.Theorems.STLSatBigOr
import CORALean.Specification.STL.Theorems.STLSatBigAnd
import CORALean.Specification.STL.Theorems.SatNext
import CORALean.Specification.STL.Theorems.SatOfPform
import CORALean.Specification.STL.Theorems.ShiftShift

/-!
# What a normal form says of a trace

[1, Lemma 2]: `ξ ⊨ₜ ⋀ᵢ ⋁ⱼ X_c^j (φᵢⱼ ∨ ϱᵢⱼ)` unfolded: each clause has a branch whose `F(0,c)` or
`G(0,c)` holds on the window `(jc, jc + c)` or whose `ϱᵢⱼ` holds at `jc`.

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". ATVA, LNCS 9938, pp. 412-427, 2016.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {X : Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.CNF.sat_toFormula (c : ℝ≥0) (cnf : STL.CNF X) (ξ : ℝ≥0 → X) :
    (cnf.toFormula c).Sat ξ ↔ ∀ clause ∈ cnf, ∃ b ∈ clause, b.Holds c ξ := by -- --- PROOF ---
  unfold STL.CNF.toFormula
  simp only [STL.Formula.sat_bigAnd, STL.Formula.sat_bigOr, STL.Formula.sat_next,
    STL.Formula.Sat, STL.Formula.sat_ofPform, Time.shift_shift]
  -- a shifted trace read at `0` is the trace read at the shift
  simp only [Time.shift, zero_add]
  exact Iff.rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
