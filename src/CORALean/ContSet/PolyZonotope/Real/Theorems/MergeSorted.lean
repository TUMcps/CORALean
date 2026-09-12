import CORALean.ContSet.PolyZonotope.Real.Operations.Merge
import CORALean.ContSet.PolyZonotope.Real.Operations.Sorted

/-!
# `merge` keeps a sorted matrix sorted

Half of what [1, Prop. 3.3] claims of its result, and the half that holds:
`mergeIdx` names the kept columns in increasing order, so the result's columns
are a subsequence of the operand's and ascend with them.

The other half — regularity — does not; `Merge.lean` says where it fails.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       12-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [Module ℝ α] in
/-- The kept columns are named in increasing order. File-local: only
`merge_sorted` below needs it. -/
theorem PolyZonotope.aux_mergeIdx_monotone {p h : ℕ} (E : Fin p → Fin h → ℕ) :
    Monotone (PolyZonotope.mergeIdx E) :=
  fun _ _ hab => ((PolyZonotope.mergeKeep E).orderIsoOfFin rfl).monotone hab


-- =======================================  MAIN THEOREM  ======================================= --

omit [Module ℝ α] in
theorem PolyZonotope.merge_sorted {pZ : PolyZonotope α} (hS : PolyZonotope.Sorted pZ.E) :
    PolyZonotope.Sorted pZ.merge.E :=
  hS.comp (PolyZonotope.aux_mergeIdx_monotone pZ.E)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
