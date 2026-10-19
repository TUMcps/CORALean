module

public import CORALean.ContDynamics.LinearSysDT.Operations.ComputeGOFloat
public import CORALean.ContSet.Interval.Float.Theorems.MatPowOuter
public import CORALean.ContSet.Interval.Float.Theorems.MatMulOuter
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint

@[expose] public section

/-!
# The float GO parameters enclose the real ones

Every parameter `computeGO` returns for the real values of the stored matrices lies in the
interval matrix `computeGOFloat` returns for it: `A{k}`, `B{k,j}`, `C{k}` and `D{k,j}`. An outer
statement; the interval matrices are not the parameters.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic

variable {n r : ℕ} {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.computeGOFloat_outer (sys : LinearSysDT 𝕋 n) (out : OutputEq 𝕋 n n r)
    (nk : ℕ) (k j : Fin nk) : -- --- CONCL ---
    let G := sys.computeGO out nk
    let F := sys.computeGOFloat out nk
    G.A k ∈ (F.A k).construct ∧ G.B k j ∈ (F.B k j).construct ∧ G.C k ∈ (F.C k).construct ∧
      G.D k j ∈ (F.D k j).construct := by -- --- PROOF ---
  intro G F
  -- a stored zero matrix reads as the zero matrix
  have hz : ∀ {a b : ℕ}, (0 : Mat ℝ a b) ∈
      (Interval.point (show Mat 𝕋 a b from fun _ _ => zero)).construct := fun {a b} => by
    have h : toRealMat (show Mat 𝕋 a b from fun _ _ => zero) = 0 := by
      funext i l
      simp [toRealMat, toReal_zero]
    rw [← h]
    exact Interval.mem_point _
  refine ⟨Interval.matPow_outer (Interval.point sys.A) (Interval.mem_point sys.A) _, ?_, ?_, ?_⟩
  · -- `B{k,j}` is a power of `A` up to the diagonal and zero beyond
    simp only [G, F, LinearSysDT.computeGO, LinearSysDT.computeGOFloat]
    by_cases h : j.val ≤ k.val
    · rw [if_pos h, if_pos h]
      exact Interval.matPow_outer (Interval.point sys.A) (Interval.mem_point sys.A) (k.val - j.val)
    · rw [if_neg h, if_neg h]
      exact hz
  · -- `C{k} = C Aᵏ`
    exact Interval.matMul_outer _ _ (Interval.mem_point out.C)
      (Interval.matPow_outer (Interval.point sys.A) (Interval.mem_point sys.A) k.val)
  · -- `D{k,j}` is `D` on the diagonal, `C A^{k-1-j}` below it and zero above
    simp only [G, F, LinearSysDT.computeGO, LinearSysDT.computeGOFloat]
    by_cases hjk : j = k
    · rw [if_pos hjk, if_pos hjk]
      exact Interval.mem_point out.D
    · rw [if_neg hjk, if_neg hjk]
      by_cases hlt : j.val < k.val
      · rw [if_pos hlt, if_pos hlt]
        exact Interval.matMul_outer _ _ (Interval.mem_point out.C)
          (Interval.matPow_outer (Interval.point sys.A) (Interval.mem_point sys.A)
            (k.val - 1 - j.val))
      · rw [if_neg hlt, if_neg hlt]
        exact hz

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
