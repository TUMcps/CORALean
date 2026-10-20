module

public import CORALean.ContSet.Conversion.Real.Operations.VPolytope_to_Interval
public import CORALean.ContSet.VPolytope.Real.Operations.LeOfForallLe
public import CORALean.ContSet.Interval.Real.Theorems.MemMat

@[expose] public section

/-!
# The interval matrix of a matrix polytope contains it

Each entry of a member is a convex combination of the same entry of the vertices (`le_of_forall_le`
at the entry functional), so lies between the least and the greatest of them. The box is the
smallest around the vertices, and so around the hull; the set of the polytope is in general a proper
subset.

## Inputs
* `P` – matrix vertex polytope

## Hypotheses
* none

## Conclusion
* polytope is contained in its interval matrix
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every member of the matrix polytope lies in its interval matrix. -/
theorem VPolytope.intervalMatrix_contains (P : VPolytope (Mat ℝ m n)) : -- --- CONCL ---
    P.construct ⊆ P.intervalMatrix.construct := by -- --- PROOF ---
  intro x hx
  refine Interval.mem_mat_iff.mpr fun i j => ?_
  have hbddA : BddAbove (Set.range fun l => P.V l i j) := (Set.finite_range _).bddAbove
  have hbddB : BddBelow (Set.range fun l => P.V l i j) := (Set.finite_range _).bddBelow
  -- the entry is below the greatest and above the least entry of the vertices
  have hup : x i j ≤ ⨆ l, P.V l i j :=
    P.le_of_forall_le (Matrix.entryLinearMap ℝ ℝ i j) (fun l => le_ciSup hbddA l) hx
  have hlo : (⨅ l, P.V l i j) ≤ x i j := by
    have h : -(x i j) ≤ -(⨅ l, P.V l i j) := P.le_of_forall_le (-Matrix.entryLinearMap ℝ ℝ i j)
      (fun l => neg_le_neg (ciInf_le hbddB l)) hx
    linarith
  simp only [VPolytope.intervalMatrix, Interval.ofCenterRadius, Matrix.sub_apply, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul]
  constructor <;> linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
