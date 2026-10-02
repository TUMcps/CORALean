import CORALean.ContSet.Interval.Float.Theorems.MemMatIff
import CORALean.ContSet.MatZonotope.Float.Operations.Point

/-!
# A stored matrix lies in its point matrix zonotope

The empty generator sum and the zero box each add nothing.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatZonotope.mem_point (A : Mat 𝕋 m n) :
    toRealMat A ∈ (MatZonotope.point A).construct := by -- --- PROOF ---
  refine ⟨toRealMat A, ⟨fun k => k.elim0, fun k => k.elim0, ?_⟩, 0, ?_, add_zero _⟩
  · simp [MatZonotope.nominal, MatZonotope.point]
  -- the zero box holds the zero matrix
  · refine Interval.mem_mat_iff.mpr fun i j => ?_
    show toReal (zero : 𝕋) ≤ 0 ∧ 0 ≤ toReal (zero : 𝕋)
    rw [toReal_zero]
    exact ⟨le_rfl, le_rfl⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
