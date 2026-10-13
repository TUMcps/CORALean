import CORALean.ContSet.Zonotope.Real.Operations.IntersectStrip
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul

/-!
# A point of one strip intersection, from the deviation of a point before it

[1, Eq. 3], one strip: a point of `intersectStrip` at the output row `c`, gain `λ`, half-width `φ`
sits at the new centre plus `κ (z₁ - p) + φ η λ` with `κ = I - λ cᵀ`, for a point `z₁` of the
zonotope before it, centre `p`, and a coefficient `η ∈ [-1, 1]` of the strip's own generator.
The step the P-radius bounds of `[1, Eq. 4]` to `[1, Alg. 2]` are chains of.

## References

* [1] V. T. H. Le, C. Stoica, T. Alamo, E. F. Camacho and D. Dumur. "Zonotopic guaranteed state
      estimation for uncertain systems". Automatica, 49(11):3418-3424, 2013.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A point of the strip intersection is `κ` of a point before it plus `φ η λ`. -/
theorem Zonotope.intersectStrip_dev (c l : Vec ℝ n) (φ y : ℝ) (Z : Zonotope (Vec ℝ n))
    {z : Vec ℝ n}
    (hz : z ∈ (Z.intersectStrip (Matrix.of fun _ => c : Mat ℝ 1 n) (fun _ => φ) (fun _ => y)
      (Matrix.of fun r _ => l r : Mat ℝ n 1)).construct) :
    ∃ z₁ ∈ Z.construct, ∃ η : ℝ, |η| ≤ 1 ∧
      z - (Z.intersectStrip (Matrix.of fun _ => c : Mat ℝ 1 n) (fun _ => φ) (fun _ => y)
        (Matrix.of fun r _ => l r : Mat ℝ n 1)).c
        = (1 - vecMulVec l c) *ᵥ (z₁ - Z.c) + (φ * η) • l := by -- --- PROOF ---
  obtain ⟨b, hb, rfl⟩ : ∃ b : Fin (Z.h + 1) → ℝ, (∀ j, |b j| ≤ 1) ∧
      z = (Z.intersectStrip (Matrix.of fun _ => c : Mat ℝ 1 n) (fun _ => φ) (fun _ => y)
        (Matrix.of fun r _ => l r : Mat ℝ n 1)).c + ∑ j : Fin (Z.h + 1),
        b j • (Z.intersectStrip (Matrix.of fun _ => c : Mat ℝ 1 n) (fun _ => φ) (fun _ => y)
        (Matrix.of fun r _ => l r : Mat ℝ n 1)).G j := hz
  -- the coefficients of the zonotope before, and of the strip's own generator
  refine ⟨Z.c + ∑ j : Fin Z.h, b (Fin.castAdd 1 j) • Z.G j, ⟨_, fun j => hb _, rfl⟩,
    b (Fin.natAdd Z.h 0), hb _, ?_⟩
  have hκ : (1 : Mat ℝ n n) - (Matrix.of fun r (_ : Fin 1) => l r) * (Matrix.of fun _ => c)
      = 1 - vecMulVec l c := by
    congr 1; ext i j; simp [Matrix.mul_apply, vecMulVec]
  -- the generators of the old zonotope sum to `κ` of the old deviation
  have h1 : ∑ j : Fin Z.h, b (Fin.castAdd 1 j) • ((1 - vecMulVec l c) *ᵥ Z.G j) =
      (1 - vecMulVec l c) *ᵥ ∑ j : Fin Z.h, b (Fin.castAdd 1 j) • Z.G j := by
    simp only [Matrix.mulVec_sum, Matrix.mulVec_smul]
  have h3 : ∑ j : Fin 1, b (Fin.natAdd Z.h j) •
      ((Matrix.of fun r (_ : Fin 1) => l r) *ᵥ Pi.single j φ) = (φ * b (Fin.natAdd Z.h 0)) • l := by
    rw [Fin.sum_univ_one]
    ext i
    simp
    ring
  rw [add_sub_cancel_left, add_sub_cancel_left, ← h1, ← h3, Fin.sum_univ_add]
  simp only [Zonotope.intersectStrip, Fin.append_left, Fin.append_right, hκ]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
