module

public import CORALean.ContDynamics.LinearSysDT.Operations.ErrMatFloat
public import CORALean.ContSet.Interval.Float.Theorems.MatMulOuter
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint

@[expose] public section

/-!
# The interval error matrix holds `A - L C`

The real `A - L C` of the real values of the stored matrices lies in `errMatFloat A L C`.

## Inputs
* `A` – float state matrix
* `L` – float gain
* `C` – float output matrix

## Hypotheses
* none

## Conclusion
* the real error matrix lies in the interval error matrix
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.errMatFloat_mem (A : Mat 𝕋 n n) (L : Mat 𝕋 n p) (C : Mat 𝕋 p n) :
    toRealMat A - toRealMat L * toRealMat C ∈
      (LinearSysDT.errMatFloat A L C).construct := by -- --- PROOF ---
  have hLC : toRealMat L * toRealMat C ∈
      (Interval.matMul (Interval.point L) (Interval.point C)).construct :=
    Interval.matMul_outer (Interval.point L) (Interval.point C)
    (Interval.mem_point L) (Interval.mem_point C)
  refine Interval.mem_mat_iff.mpr fun i j => ?_
  obtain ⟨h₁, h₂⟩ := Interval.mem_mat_iff.mp hLC i j
  have hA : toRealMat A i j = toReal (A i j) := rfl
  refine ⟨le_trans (subDown_le_sub _ _) ?_, le_trans ?_ (sub_le_subUp _ _)⟩
  · simp only [Matrix.sub_apply, hA]
    linarith
  · simp only [Matrix.sub_apply, hA]
    linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
