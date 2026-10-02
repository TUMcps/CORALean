import CORALean.ContSet.MatZonotope.Float.Operations.MatPow
import CORALean.ContSet.MatZonotope.Float.Theorems.MatMulOuter
import CORALean.ContSet.MatZonotope.Float.Theorems.MemPoint

/-!
# Every power of a member lies in the matrix zonotope's power

Induction on the order, `matMul_outer` at each step, as `Real.Zonotope.matPow_outer`;
the base case is the stored identity, which reads back as `1`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The stored identity block reads back as the real identity matrix. -/
theorem MatZonotope.aux_toRealMat_diagonalBlock_one :
    toRealMat (diagonalBlock fun _ : Fin n => (one : 𝕋)) = (1 : Mat ℝ n n) := by
  funext i j
  rw [toRealMat, toReal_diagonalBlock]
  simp [toRealVec, toReal_one, Matrix.one_apply, Matrix.diagonal_apply]


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatZonotope.matPow_outer (M : MatZonotope 𝕋 n n) {A : Mat ℝ n n}
    (hA : A ∈ M.construct) (k : ℕ) : A ^ k ∈ (M.matPow k).construct := by -- --- PROOF ---
  induction k with
  | zero =>
    rw [pow_zero, ← MatZonotope.aux_toRealMat_diagonalBlock_one (𝕋 := 𝕋)]
    exact MatZonotope.mem_point (diagonalBlock fun _ : Fin n => (one : 𝕋))
  -- the base paired with the previous power, which is what `matMul` bounds
  | succ k ih =>
    rw [pow_succ']
    show A * A ^ k ∈ (MatZonotope.matMul M (M.matPow k)).materialise.construct
    rw [MatZonotope.materialise_eq]
    exact MatZonotope.matMul_outer M (M.matPow k) (Set.mem_biUnion hA ⟨A ^ k, ih, rfl⟩)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
