import CORALean.ContSet.Capsule.Real.Operations.MtimesCora
import CORALean.ContSet.Capsule.Real.Theorems.MtimesOuter

/-!
# CORA's `capsule/mtimes` radius is unsound for a contraction

CORA's `@capsule/mtimes.m` sets `C.c = M c`, `C.g = M g` and `C.r = r · max(eig(M Mᵀ))`. The
eigenvalues of `M Mᵀ` are the *squares* `σᵢ²` of the singular values, while the image of a ball of
radius `r` has radius `r σ_max`. So CORA's radius is too small exactly when `σ_max < 1`: `M = ½ I`
has `M Mᵀ = ¼ I`, so CORA answers `r/4` for a true `r/2`. `Capsule.mtimes` scales by the Frobenius
bound of `σ_max` instead, and `Capsule.mtimes_outer` is the sound statement.

Stated with the eigenvalue `lam` as a parameter, since only its value on this `M` matters. Not
run in CORA; read from the source.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- For `M = ½` in dimension one, `M Mᵀ = ¼`, so `lam = ¼`, and CORA's capsule misses the image
of the capsule with centre `0`, no segment and radius `1` (the point `1` maps to `½`, outside the
ball of radius `¼`). -/
theorem Capsule.mtimes_cora_counterexample :
    ∃ (M : Mat ℝ 1 1) (C : Capsule 1), M * M.transpose = Matrix.of (fun _ _ => (1 / 4 : ℝ)) ∧
      ¬ (fun x => M.mulVec x) '' C.construct ⊆
        (C.mtimesCora M (1 / 4)).construct := by -- --- PROOF ---
  refine ⟨Matrix.of fun _ _ => (1 / 2 : ℝ), ⟨0, 0, 1⟩, ?_, fun h => ?_⟩
  · ext i j
    fin_cases i; fin_cases j
    simp [Matrix.mul_apply]; norm_num
  · have hx : (fun _ => (1 : ℝ) : Vec ℝ 1) ∈ (Capsule.mk (0 : Vec ℝ 1) 0 1).construct :=
      ⟨0, by simp, by simp⟩
    obtain ⟨t, -, ht⟩ := h ⟨_, hx, rfl⟩
    simp [Capsule.mtimesCora, Matrix.mulVec, dotProduct] at ht
    norm_num at ht

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
