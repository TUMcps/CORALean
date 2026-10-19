module

public import CORALean.ContSet.Capsule.Real.Capsule
public import Mathlib.Data.Matrix.Mul
public import CORALean.ContSet.Capsule.Real.Theorems.MtimesOuter

@[expose] public section

/-!
# CORA's `capsule/mtimes` radius, as printed

Center and generator mapped, radius `r · lam`, with `lam` the largest eigenvalue of `M Mᵀ`. Kept
only so that `Capsule.mtimes_cora_counterexample` can state that it is unsound; `Capsule.mtimes`
is the sound operation.

# CORA's `capsule/mtimes` radius is unsound for a contraction

CORA's `@capsule/mtimes.m` sets `C.c = M c`, `C.g = M g` and `C.r = r · max(eig(M Mᵀ))`. The
eigenvalues of `M Mᵀ` are the *squares* `σᵢ²` of the singular values, while the image of a ball of
radius `r` has radius `r σ_max`. So CORA's radius is too small exactly when `σ_max < 1`: `M = ½ I`
has `M Mᵀ = ¼ I`, so CORA answers `r/4` for a true `r/2`. `Capsule.mtimes` scales by the Frobenius
bound of `σ_max` instead, and `Capsule.mtimes_outer` is the sound statement.

Stated with the eigenvalue `lam` as a parameter, since only its value on this `M` matters. Not
run in CORA; read from the source.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* CORA's `mtimes` radius misses part of the image under a contraction
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m n : ℕ}


-- The model: CORA's code as printed, kept only to be refuted.
/-- CORA's `mtimes` as printed: radius `r · lam`, with `lam` the largest eigenvalue of `M Mᵀ`. -/
def Capsule.mtimesCora (M : Mat ℝ m n) (C : Capsule n) (lam : ℝ) : Capsule m :=
  ⟨M.mulVec C.c, M.mulVec C.g, C.r * lam⟩

end CORALean.Real

namespace CORALean.Real

variable {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- For `M = ½` in dimension one, `M Mᵀ = ¼`, so `lam = ¼`, and CORA's capsule misses the image
of the capsule with center `0`, no segment and radius `1` (the point `1` maps to `½`, outside the
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
