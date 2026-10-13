import CORALean.ContDynamics.LinearARX.Operations.ComputeGOFloat
import CORALean.ContDynamics.LinearARX.Theorems.SumRangeFloatMem
import CORALean.ContSet.Interval.Float.Theorems.MatPowOuter
import CORALean.ContSet.Interval.Float.Theorems.MatMulOuter
import CORALean.ContSet.Interval.Float.Theorems.MemPoint

/-!
# The float output GO parameters enclose the real ones

CORA's `computeGO` [1]: every parameter it returns for the real values of the stored matrices lies
in the interval matrix `computeGOFloat` returns for it: `C{k}` and `D{k,i}`. An outer statement;
the interval matrices are not the parameters.

## References

* [1] `contDynamics/@linearARX/computeGO.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {dy du p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearARX.computeGOFloat_outer (sys : LinearARX 𝕋 dy du p) (nk : ℕ) (k i : Fin nk) :
    let G := sys.computeGO nk
    let F := sys.computeGOFloat nk
    G.C k ∈ (F.C k).construct ∧ G.D k i ∈ (F.D k i).construct := by -- --- PROOF ---
  intro G F
  -- a stored zero matrix reads as the zero matrix
  have hz : ∀ {a b : ℕ}, (0 : Mat ℝ a b) ∈
      (Interval.point (show Mat 𝕋 a b from fun _ _ => zero)).construct := fun {a b} => by
    have h : toRealMat (show Mat 𝕋 a b from fun _ _ => zero) = 0 := by
      funext r l
      simp [toRealMat, toReal_zero]
    rw [← h]
    exact Interval.mem_point _
  have hA := Interval.matPow_outer (Interval.point sys.toLinearSysDT.A)
    (Interval.mem_point sys.toLinearSysDT.A)
  refine ⟨Interval.matMul_outer _ _ (Interval.mem_point sys.outputEq.C) (hA k.val), ?_⟩
  -- the sum over steps, each term the sum over lags
  refine LinearARX.sumRangeFloat_mem _ _ (fun t => ?_) k.val
  -- the sum over the lags, as a sum over an index range
  have hlag : (∑ j : Fin (p + 1), if t + p - j.val = i.val then
      toRealMat sys.outputEq.C * toRealMat sys.toLinearSysDT.A ^ (k.val - 1 - t)
        * toRealMat (sys.inputMat j) else 0) =
      ∑ j ∈ Finset.range (p + 1), if hj : j < p + 1 then
        (if t + p - j = i.val then toRealMat sys.outputEq.C *
          toRealMat sys.toLinearSysDT.A ^ (k.val - 1 - t) * toRealMat (sys.inputMat ⟨j, hj⟩)
        else 0) else 0 := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => if hj : j < p + 1 then
      (if t + p - j = i.val then toRealMat sys.outputEq.C *
        toRealMat sys.toLinearSysDT.A ^ (k.val - 1 - t) * toRealMat (sys.inputMat ⟨j, hj⟩)
      else 0) else 0) (p + 1)]
    exact Finset.sum_congr rfl fun j _ => by simp
  show (∑ j : Fin (p + 1), if t + p - j.val = i.val then
      toRealMat sys.outputEq.C * toRealMat sys.toLinearSysDT.A ^ (k.val - 1 - t)
        * toRealMat (sys.inputMat j) else 0) ∈ _
  rw [hlag]
  refine LinearARX.sumRangeFloat_mem _ _ (fun j => ?_) (p + 1)
  -- one term: the product, or zero
  by_cases hj : j < p + 1
  · simp only [dif_pos hj]
    by_cases ht : t + p - j = i.val
    · simp only [if_pos ht]
      exact Interval.matMul_outer _ _ (Interval.matMul_outer _ _
        (Interval.mem_point sys.outputEq.C) (hA _)) (Interval.mem_point _)
    · simp only [if_neg ht]
      exact hz
  · simp only [dif_neg hj]
    exact hz

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
