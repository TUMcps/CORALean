module

public import CORALean.Specification.STL.Operations.CNFNext
public import CORALean.Specification.STL.Theorems.CNFSatToFormula
public import CORALean.Specification.STL.Definitions.BranchHolds
public import CORALean.Specification.STL.Theorems.ShiftShift

@[expose] public section

/-!
# The next-operator on a normal form

[1, Sec. 4.1]: `ξ ⊨ₜ X_c a ⇔ ⟨ξ⟩_c ⊨ₜ a` for `a.next`: raising every `j` reads the trace shifted
by `c`.

## Inputs
* `c` – time step
* `a` – normal form
* `ξ` – trace

## Hypotheses
* none

## Conclusion
* the raised form holds iff the form holds on the shifted trace

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


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A raised power reads the shifted trace. -/
theorem STL.Branch.aux_holds_shift (c : ℝ≥0) (b : STL.Branch X) (ξ : ℝ≥0 → X) :
    ({ b with j := b.j + 1 } : STL.Branch X).Holds c ξ ↔ b.Holds c (Time.shift ξ c) := by
  -- the argument `t + (j + 1) c` is `t + j c + c`
  have e₀ : ((b.j + 1 : ℕ) : ℝ≥0) * c = b.j * c + c := by push_cast; ring
  unfold STL.Branch.Holds
  simp only [Time.shift, e₀, add_assoc]


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.CNF.sat_next (c : ℝ≥0) (a : STL.CNF X) (ξ : ℝ≥0 → X) :
    (a.next.toFormula c).Satisfies ξ ↔ (a.toFormula c).Satisfies (Time.shift ξ c) := by
  rw [STL.CNF.sat_toFormula, STL.CNF.sat_toFormula]
  simp only [STL.CNF.next, List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, exists_exists_and_eq_and, STL.Branch.aux_holds_shift]


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
