module

public import CORALean.Specification.STL.Operations.CNFToFormula
public import CORALean.Specification.STL.Definitions.BranchHolds
public import CORALean.Specification.STL.Theorems.STLSatBigOr
public import CORALean.Specification.STL.Theorems.STLSatBigAnd
public import CORALean.Specification.STL.Theorems.SatNext
public import CORALean.Specification.STL.Theorems.SatOfPform
public import CORALean.Specification.STL.Theorems.ShiftShift

@[expose] public section

/-!
# What a normal form says of a trace

[1, Lemma 2]: `ξ ⊨ₜ ⋀ᵢ ⋁ⱼ X_c^j (φᵢⱼ ∨ ϱᵢⱼ)` unfolded: each clause has a branch whose `F(0,c)` or
`G(0,c)` holds on the window `(jc, jc + c)` or whose `ϱᵢⱼ` holds at `jc`.

## Inputs
* `c` – time step
* `cnf` – normal form
* `ξ` – trace

## Hypotheses
* none

## Conclusion
* the formula holds iff every clause has a holding branch

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
