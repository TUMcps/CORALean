import CORALean.ContSet.ConZonotope.Real.Operations.Eliminate
import CORALean.ContSet.ConZonotope.Real.Theorems.PartialSolveZeroCol
import CORALean.ContSet.ConZonotope.Real.Theorems.PartialSolveZeroRow
import CORALean.ContSet.ConZonotope.Real.Theorems.MemOfMatDropIff

/-!
# Partial solve, then drop, is `eliminate`

[1, Sec. 4.2]: removing the zero column and row of the partial-solve `Z̃` leaves one constraint
and one generator fewer, which is `ConZonotope.eliminate`, defined from the same `Λ_G` and `Λ_A`
in closed form. The two have the same set; their `ofMat` systems differ by the dropped index.

## References

* [1] J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes:
      A new tool for set-based estimation and fault detection". Automatica, 69:126-136,
      2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 4.2]: dropping the zero column and row of the partial-solve `Z̃` is `eliminate`. -/
theorem ConZonotope.partialSolve_eq_eliminate {n q h : ℕ} (c : Vec ℝ n)
    (G : Fin h → Vec ℝ n) (A : Mat ℝ q h) (b : Vec ℝ q) (r : Fin q) (j : Fin h)
    (hAj : A r j ≠ 0) :
    (ConZonotope.partialSolve c G A b r j).construct
      = (ConZonotope.eliminate c G A b r j).construct := by -- --- PROOF ---
  obtain ⟨hG, hA⟩ := ConZonotope.partialSolve_zero_col G A r j hAj
  obtain ⟨hr, hb⟩ := ConZonotope.partialSolve_zero_row A b r j hAj
  ext x
  unfold ConZonotope.partialSolve ConZonotope.constraintReduce
  rw [ConZonotope.mem_ofMat_drop_iff _ _ _ _ r j hG hA hr hb]
  unfold ConZonotope.eliminate
  -- the dropped system is `eliminate`'s, entry for entry
  have hc : c + ConZonotope.partialSolveΛG G A r j *ᵥ b = c + b r • ((A r j)⁻¹ • G j) := by
    rw [ConZonotope.partialSolveΛG_mulVec]
  have hG' : (fun l => G l - ConZonotope.partialSolveΛG G A r j *ᵥ fun k => A k l)
      = fun l => G l - A r l • ((A r j)⁻¹ • G j) := by
    funext l; rw [ConZonotope.partialSolveΛG_mulVec]
  have hA' : A - ConZonotope.partialSolveΛA A r j * A
      = fun i l => A i l - A i j * (A r j)⁻¹ * A r l := by
    funext i l; rw [Matrix.sub_apply, ConZonotope.partialSolveΛA_mul]
  have hb' : b - ConZonotope.partialSolveΛA A r j *ᵥ b
      = fun i => b i - A i j * (A r j)⁻¹ * b r := by
    funext i; rw [Pi.sub_apply, ConZonotope.partialSolveΛA_mulVec]
  rw [hc, hG', hA', hb']

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
