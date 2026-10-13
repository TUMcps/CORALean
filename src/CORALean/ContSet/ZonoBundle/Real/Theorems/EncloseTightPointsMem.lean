import CORALean.ContSet.ZonoBundle.Real.Operations.EncloseTightPoints
import CORALean.ContSet.Interval.Real.Theorems.EnclosePointsOuter
import CORALean.ContSet.Zonotope.Real.Theorems.EnclosePointsStursbergMem
import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact

/-!
# Every point lies in the bundle of `encloseTightPoints`

Every point of `V` lies in each zonotope collected: in `W{i} * zonotope(box)` because `pinv(W{i}) v`
is in the box of the `pinv(W{i}) V` and `W{i} pinv(W{i}) v = v` for an invertible `W{i}`; and in
the Stursberg zonotope for every orthogonal `U`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n r N : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.encloseTightPoints_mem [NeZero N] (V : Fin N → Vec ℝ n)
    (W : Fin r → Mat ℝ n n) (hW : ∀ i, IsUnit (W i).det) {U : Mat ℝ n n} (hU : U * Uᵀ = 1)
    (j : Fin N) : V j ∈ (ZonoBundle.encloseTightPoints V W U).construct := by -- --- PROOF ---
  refine Set.mem_iInter.mpr fun i => ?_
  induction i using Fin.lastCases with
  | last =>
    -- the Stursberg zonotope
    simp only [ZonoBundle.encloseTightPoints, Fin.snoc_last]
    exact Zonotope.enclosePointsStursberg_mem V hU j
  | cast i =>
    -- the box in `W{i}`'s coordinates, mapped back
    simp only [ZonoBundle.encloseTightPoints, Fin.snoc_castSucc]
    rw [← Zonotope.mtimes_exact]
    refine ⟨(W i)⁻¹ *ᵥ V j,
      Interval.zonotope_contains _ (Interval.enclosePoints_outer (fun j => (W i)⁻¹ *ᵥ V j) j), ?_⟩
    show W i *ᵥ ((W i)⁻¹ *ᵥ V j) = V j
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hW i), Matrix.one_mulVec]


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
