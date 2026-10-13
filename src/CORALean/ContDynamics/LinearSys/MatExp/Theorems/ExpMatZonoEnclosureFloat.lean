module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpMatZonoEnclosureFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsEntryLeNorm
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpMatZonoRemainderFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpMatZonoTaylorFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpRemainderBoundFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormExpSubExpTaylorLe
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormUpperBoundFloat
public import CORALean.ContSet.Interval.Real.Theorems.NormLeAbsMax
public import CORALean.ContSet.Zonotope.Float.Theorems.MatPlusIntervalOuter

@[expose] public section

/-!
# The exponential of every member lies in the float matrix-zonotope enclosure

`Real.MatExp.exp_mem_expMatZonoEnclosure` in floats: the truncation lands in the float
Taylor sum, and what it left out is a matrix of entries within the tail bound, taken
uniformly at `normUpperBound` of the zonotope's `interval` and rounded to a float by
`expRemainderBound_le`; `plusInterval_outer` adds the two.

`hε` asks `1/2`, not `< 1`, for `expIntervalEnclosure`'s reason: the float bound's
geometric factor is the constant `2`. It is checkable from the zonotope alone.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix NormedSpace Pointwise FloatOps SoundFloatArithmetic

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.exp_mem_expMatZonoEnclosure (M : Zonotope (Mat 𝕋 n n)) (η : ℕ)
    {A : Mat ℝ n n} (hA : A ∈ M.construct)
    (hε : toReal (MatExp.normUpperBound M.matInterval) / ((η : ℝ) + 2) ≤ 1 / 2) :
    exp A ∈ (MatExp.expMatZonoEnclosure M η).construct := by -- --- PROOF ---
  have hnorm : ‖A‖ ≤ toReal (MatExp.normUpperBound M.matInterval) :=
    le_trans (Real.Interval.norm_le_absMax (Zonotope.matInterval_contains M hA))
      (MatExp.norm_absMax_le_normUpperBound _)
  have hnn : (0 : ℝ) ≤ toReal (MatExp.normUpperBound M.matInterval) := le_trans
    (norm_nonneg A) hnorm
  have hfrac : ‖A‖ / ((η : ℝ) + 2) ≤ toReal (MatExp.normUpperBound M.matInterval) / ((η : ℝ) + 2) :=
    by gcongr
  have hεA : ‖A‖ / ((η : ℝ) + 2) < 1 := lt_of_le_of_lt (le_trans hfrac hε) (by norm_num)
  -- the tail at `A`, widened to the one float bound the whole zonotope answers for
  have htail : ‖exp A - Real.MatExp.expTaylor A η‖
      ≤ toReal (MatExp.expRemainderBound (MatExp.normUpperBound M.matInterval) η) :=
    le_trans (Real.norm_exp_sub_expTaylor_le A η hεA) (MatExp.expRemainderBound_le η hnorm hnn hε)
  have hrem : exp A - Real.MatExp.expTaylor A η ∈ (MatExp.expMatZonoRemainder n
      (MatExp.expRemainderBound (MatExp.normUpperBound M.matInterval) η)).construct :=
    MatExp.mem_expMatZonoRemainder fun i j => le_trans (Real.abs_entry_le_norm _ i j) htail
  have hmem := Zonotope.matPlusInterval_outer _ _
    (Set.add_mem_add (MatExp.expTaylor_mem_expMatZonoTaylor M hA η) hrem)
  have heq : Real.MatExp.expTaylor A η + (exp A - Real.MatExp.expTaylor A η) = exp A := by abel
  rw [heq] at hmem
  exact hmem

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
