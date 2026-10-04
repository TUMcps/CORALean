import CORALean.Specification.STL.Operations.SampToCNF
import CORALean.Specification.STL.Theorems.CNFSatAppend
import CORALean.Specification.STL.Theorems.CNFSatOr
import CORALean.Specification.STL.Theorems.CNFSatNext
import CORALean.Specification.STL.Theorems.SatOfPform
import CORALean.Specification.STL.Theorems.SatOr
import CORALean.Specification.STL.Theorems.SatAnd
import CORALean.Specification.STL.Theorems.SatNext

/-!
# The normal form is equivalent

[1, Sec. 4.1]: `s.toCNF true` is equivalent to `s` and `s.toCNF false` to `¬s`, at every time step
`c` and on every trace: `∧` appends clauses, `∨` merges them pairwise, `X_c` shifts the trace, a
negation is pushed in.

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

theorem STL.Samp.sat_toCNF (c : ℝ≥0) (s : STL.Samp X) (pos : Bool) (ξ : ℝ≥0 → X) :
    ((s.toCNF pos).toFormula c).Sat ξ ↔
      if pos then (s.toFormula c).Sat ξ else ¬ (s.toFormula c).Sat ξ := by -- --- PROOF ---
  induction s generalizing pos ξ with
  | lit ϱ =>
    rw [STL.CNF.sat_toFormula]
    cases pos <;> simp [STL.Samp.toCNF, STL.Samp.toFormula, STL.Formula.sat_ofPform,
      STL.Branch.Holds, Pform.Sat]
  | not s ih =>
    cases pos
    · simpa [STL.Samp.toCNF, STL.Samp.toFormula, STL.Formula.Sat] using ih true ξ
    · simpa [STL.Samp.toCNF, STL.Samp.toFormula, STL.Formula.Sat] using ih false ξ
  | and s t ihs iht =>
    cases pos
    · -- `¬(s ∧ t)` is `¬s ∨ ¬t`
      simp only [STL.Samp.toCNF, STL.CNF.sat_or, ihs, iht, STL.Samp.toFormula,
        STL.Formula.sat_and]
      exact not_and_or.symm
    · simp only [STL.Samp.toCNF, STL.CNF.sat_append, ihs, iht, if_true, STL.Samp.toFormula,
        STL.Formula.sat_and]
  | or s t ihs iht =>
    cases pos
    · -- `¬(s ∨ t)` is `¬s ∧ ¬t`
      simp only [STL.Samp.toCNF, STL.CNF.sat_append, ihs, iht, STL.Samp.toFormula,
        STL.Formula.sat_or]
      exact not_or.symm
    · simp only [STL.Samp.toCNF, STL.CNF.sat_or, ihs, iht, if_true, STL.Samp.toFormula,
        STL.Formula.sat_or]
  | next s ih =>
    simp only [STL.Samp.toCNF, STL.CNF.sat_next, ih, STL.Samp.toFormula, STL.Formula.sat_next]
  | fin ϱ =>
    -- the window operators swap under negation, and the point part is `⊥`
    rw [STL.CNF.sat_toFormula]
    cases pos
    · simp [STL.Samp.toCNF, STL.Samp.toFormula, STL.Formula.Sat, STL.Formula.sat_ofPform,
        STL.Branch.Holds, Pform.Sat, Time.shift]
    · simp [STL.Samp.toCNF, STL.Samp.toFormula, STL.Formula.Sat, STL.Formula.sat_ofPform,
        STL.Branch.Holds, Pform.Sat, Time.shift]
  | glob ϱ =>
    rw [STL.CNF.sat_toFormula]
    cases pos
    · simp [STL.Samp.toCNF, STL.Samp.toFormula, STL.Formula.Sat, STL.Formula.sat_ofPform,
        STL.Branch.Holds, Pform.Sat, Time.shift]
    · simp [STL.Samp.toCNF, STL.Samp.toFormula, STL.Formula.Sat, STL.Formula.sat_ofPform,
        STL.Branch.Holds, Pform.Sat, Time.shift]


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
