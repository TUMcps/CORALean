module

public import CORALean.ContSet.PolyZonotope.Real.Operations.EvalPolySort
public import CORALean.ContSet.PolyZonotope.Real.Operations.EvalPolySortP
public import CORALean.ContSet.PolyZonotope.Real.Operations.IsSorted
public import CORALean.ContSet.PolyZonotope.Real.Theorems.SortPlusSorted

@[expose] public section

/-!
# [1, Alg. 2] returns a sorted matrix

The half of [1, Prop. 3.5]'s *regular and sorted* that holds. Every term is a
`sortPlus`, which sorts, and the constant term is a `shift`, which leaves the
exponent matrix alone; an empty coefficient list gives no columns to order.

Regularity does not follow, and for the reason `Merge.lean` gives: no two
columns are equal (`merge_col_injective` applies here unchanged), but an
all-zero column would survive — and cannot arise, since [1, Alg. 2]'s operand is
regular and `sq` adds a non-zero column to every exponent it produces.

## Inputs
* `pZ` – polynomial zonotope
* `coeffs` – coefficient vectors

## Hypotheses
* none

## Conclusion
* the exponent matrix of the result is sorted

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural Network Verification
      using Sensitivity Analysis". Proceedings of the 26th ACM International Conference on Hybrid
      Systems: Computation and Control, 2023.
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

-- file-local: only `evalPolySort_sorted` below needs it
/-- Every tail is a `sortPlus`, or else empty. -/
theorem PolyZonotope.aux_evalPolySortTail_sorted (pZ : PolyZonotope (Vec ℝ n))
    (coeffs : List (Vec ℝ n)) (k : ℕ) :
    PolyZonotope.IsSorted (pZ.evalPolySortTailP coeffs k).1.E := by
  match coeffs with
  | [] => exact fun a _ _ => Fin.elim0 a
  | _ :: rest => exact PolyZonotope.sortPlus_sorted _ _ _


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.evalPolySort_sorted (pZ : PolyZonotope (Vec ℝ n))
    (coeffs : List (Vec ℝ n)) : PolyZonotope.IsSorted (pZ.evalPolySort coeffs).E := by
  match coeffs with
  | [] => exact fun a _ _ => Fin.elim0 a
  | _ :: rest => exact PolyZonotope.aux_evalPolySortTail_sorted pZ rest 0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
