module

public import CORALean.ContSet.HPolytope.Real.Operations.Basic
public import CORALean.ContSet.HPolytope.Real.Theorems.Basic
public import CORALean.ContSet.HPolytope.Real.Operations.RowLin
public import CORALean.ContSet.ContSet.Theorems.SupportFuncLeCoeIff
public import CORALean.Global.DropIdx

@[expose] public section

/-!
# A redundant halfspace, by its support function

[1, Eq. 1]: the `j`-th halfspace of `⟨A, b⟩` is redundant — dropping it leaves the set — exactly
when the support function in the direction of its normal is the same with and without it. Bounded
or not, degenerate or not, empty or not, as the paper says: the extended reals take the
unbounded and the empty case.

## Inputs
* `A` – `q × n` matrix
* `b` – offset vector of length `q`
* `j` – index below `q`

## Hypotheses
* none

## Conclusion
* dropping row `j` keeps the polytope iff the support function along row `j` is unchanged

## References

* [1] M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral
      Operations in CORA 2024". In Proc. of the 11th International Workshop on Applied
      Verification of Continuous and Hybrid Systems (ARCH24), EPiC Series in Computing,
      vol. 103, pp. 163-181, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {q n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.ineqs_eq_drop_iff_supportFunc (A : Mat ℝ q n) (b : Vec ℝ q)
    (j : Fin q) : -- --- CONCL ---
    let D := HPolytope.ineqs (A.submatrix (dropIdx j) id) (fun i => b (dropIdx j i))
    (HPolytope.ineqs A b).construct
        = D.construct ↔
      supportFunc (HPolytope.ineqs A b).construct (HPolytope.rowLin A j)
        = supportFunc D.construct (HPolytope.rowLin A j) := by -- --- PROOF ---
  intro D
  constructor
  · intro h
    rw [h]
  · intro h
    -- dropping a row only enlarges the set
    have hsub : (HPolytope.ineqs A b).construct ⊆ D.construct := fun x hx =>
      HPolytope.mem_ineqs_iff.mpr fun i => HPolytope.mem_ineqs_iff.mp hx (dropIdx j i)
    -- the full polytope sits below `b j`, so the smaller support function does too
    have hle : supportFunc (HPolytope.ineqs A b).construct (HPolytope.rowLin A j) ≤ (b j : EReal) :=
      supportFunc_le_coe_iff.mpr fun x hx => HPolytope.mem_ineqs_iff.mp hx j
    rw [h] at hle
    have hrow := supportFunc_le_coe_iff.mp hle
    refine Set.Subset.antisymm hsub fun x hx => ?_
    rw [HPolytope.mem_ineqs_iff]
    exact (forall_dropIdx_iff j).mpr ⟨hrow x hx, fun i => HPolytope.mem_ineqs_iff.mp hx i⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
