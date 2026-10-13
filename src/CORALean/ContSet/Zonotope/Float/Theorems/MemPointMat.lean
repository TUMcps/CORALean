import CORALean.ContSet.Interval.Float.Theorems.MemMatIff
import CORALean.ContSet.Zonotope.Float.Operations.PointMat

/-!
# A stored matrix lies in its point matrix zonotope

The empty generator sum and the zero box each add nothing.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   09-October-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.mem_pointMat (A : Mat 𝕋 m n) :
    toRealMat A ∈ (Zonotope.pointMat A).construct := by -- --- PROOF ---
  refine ⟨toRealMat A, ⟨fun k => k.elim0, fun k => k.elim0, ?_⟩, 0, ?_, add_zero _⟩
  · -- no generators, so the sum is empty
    exact (add_zero (toRealMat A)).symm.trans
      (congrArg (toRealMat A + ·) (Finset.sum_eq_zero fun k _ => Fin.elim0 k).symm)
  -- the zero box holds the zero matrix
  · refine Interval.mem_mat_iff.mpr fun i j => ?_
    show toReal (zero : 𝕋) ≤ 0 ∧ 0 ≤ toReal (zero : 𝕋)
    rw [toReal_zero]
    exact ⟨le_rfl, le_rfl⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
