module

public import CORALean.ContSet.Zonotope.Real.Operations.Volume
public import CORALean.ContSet.Zonotope.Real.Operations.IntersectStrip
public import CORALean.ContSet.Zonotope.Real.Theorems.VolumeSumSnoc
public import CORALean.ContSet.Zonotope.Real.Theorems.DetColsSnocOneSubVecMulVec
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

@[expose] public section

/-!
# The volume of the zonotope that bounds a zonotope-strip intersection, with determinants

The volume formula of [1, Sec. 6.1] for `p̂(λ) ⊕ Ĥ(λ) Bʳ⁺¹`, before the unit vectors `v_i` are
introduced: `Σ 2ⁿ |1 - cᵀλ| |det A_i| + Σ 2ⁿ |det [B_i σλ]|`, `A_i` the `n` and `B_i` the `n - 1`
generators a subset of `H` picks out. The volume is `Zonotope.volume`, the sum of `|det|` over the
`n`-subsets of generators that the paper quotes as well known, here for `intersectStrip` at one
strip; the first sum's factor is `det (I - λcᵀ) = 1 - cᵀλ`, and in the second `I - λcᵀ` is dropped
by column operations.

## Inputs
* `Z` – zonotope
* `c` – strip direction
* `l` – gain vector
* `σ` – strip radius
* `d` – strip offset

## Hypotheses
* none

## Conclusion
* the volume of the strip intersection is a sum of determinants

## References

* [1] T. Alamo, J. M. Bravo and E. F. Camacho. "Guaranteed state estimation by zonotopes".
      Automatica, 2005.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.volume_intersectStrip_det (Z : Zonotope (Vec ℝ (m+1))) (c l : Vec ℝ (m+1))
    (σ d : ℝ) : -- --- CONCL ---
    (Zonotope.intersectStrip (Matrix.of fun _ j => c j : Mat ℝ 1 (m+1)) (fun _ => σ) (fun _ => d)
        (Matrix.of fun i _ => l i : Mat ℝ (m+1) 1) Z).volume =
      ENNReal.ofReal (
        (∑ S : Finset (Fin Z.h), if hS : S.card = m + 1 then
          2 ^ (m+1) * |1 - c ⬝ᵥ l| *
            |(Matrix.of fun i k => Z.G (S.orderEmbOfFin hS k) i : Mat ℝ (m+1) (m+1)).det|
          else 0) +
        (∑ T : Finset (Fin Z.h), if hT : T.card = m then
          2 ^ (m+1) * |(colsSnoc (fun k => Z.G (T.orderEmbOfFin hT k)) (σ • l)).det|
          else 0)) := by -- --- PROOF ---
  -- the strip is one row `cᵀ` and the gain one column `λ`
  set Λ : Mat ℝ (m+1) 1 := Matrix.of fun i _ => l i with hΛ
  set C : Mat ℝ 1 (m+1) := Matrix.of fun _ j => c j with hC
  have hTΛC : (1 - Λ * C : Mat ℝ (m+1) (m+1)) = 1 - Matrix.vecMulVec l c := by
    ext i j; simp [hΛ, hC, Matrix.mul_apply, Matrix.vecMulVec_apply]
  -- `det (I - λcᵀ) = 1 - cᵀλ`, by the matrix determinant lemma
  have hdet1 : (1 - Matrix.vecMulVec l c : Mat ℝ (m+1) (m+1)).det = 1 - c ⬝ᵥ l := by
    have h : (1 - Matrix.vecMulVec l c : Mat ℝ (m+1) (m+1)) =
        1 + Matrix.replicateCol Unit (-l) * Matrix.replicateRow Unit c := by
      ext i j; simp [Matrix.vecMulVec_apply, Matrix.replicateCol, Matrix.replicateRow,
        Matrix.mul_apply, Matrix.one_apply, sub_eq_add_neg]
    rw [h, Matrix.det_one_add_replicateCol_mul_replicateRow]
    simp [dotProduct_neg, sub_eq_add_neg]
  -- the volume sum, split at the strip generator, which is the last one
  unfold Zonotope.volume
  congr 1
  have hsplit := Zonotope.volume_sum_snoc (r := Z.h) (m := m)
    (Fin.append (fun j => (1 - Λ * C) *ᵥ Z.G j) (fun i : Fin 1 => Λ *ᵥ Pi.single i σ))
  have hG1 : ∀ j : Fin Z.h, Fin.append (fun j => (1 - Λ * C) *ᵥ Z.G j)
      (fun i : Fin 1 => Λ *ᵥ Pi.single i σ) (Fin.castSucc j) = (1 - Λ * C) *ᵥ Z.G j :=
    fun j => Fin.append_left _ _ j
  have hG2 : Fin.append (fun j => (1 - Λ * C) *ᵥ Z.G j)
      (fun i : Fin 1 => Λ *ᵥ Pi.single i σ) (Fin.last Z.h) = σ • l := by
    have := Fin.append_right (fun j => (1 - Λ * C) *ᵥ Z.G j)
      (fun i : Fin 1 => Λ *ᵥ Pi.single i σ) 0
    refine this.trans ?_
    ext i; simp [hΛ, Matrix.mulVec, dotProduct, Pi.single_apply, mul_comm]
  -- the first generators are mapped by `I - λcᵀ`, the last is `σλ`
  refine Eq.trans (congrArg (2 ^ (m+1) * ·) hsplit) ?_
  simp only [hG1, hG2]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · -- subsets of the old generators: the factor `det (I - λcᵀ)` comes out
    refine Finset.sum_congr rfl fun S _ => ?_
    by_cases hS : S.card = m + 1
    · simp only [hS, dif_pos]
      have hM : (Matrix.of fun i k => ((1 - Λ * C) *ᵥ Z.G (S.orderEmbOfFin hS k)) i :
          Mat ℝ (m+1) (m+1)) = (1 - Λ * C) * Matrix.of fun i k => Z.G (S.orderEmbOfFin hS k) i := by
        ext i k; simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
      rw [hM, Matrix.det_mul, hTΛC, hdet1, abs_mul]
      ring
    · simp [hS]
  · -- subsets with the strip generator: `I - λcᵀ` can be dropped
    refine Finset.sum_congr rfl fun T _ => ?_
    by_cases hT : T.card = m
    · simp only [hT, dif_pos]
      have hB : (fun k => (1 - Λ * C) *ᵥ Z.G (T.orderEmbOfFin hT k)) =
          fun k => (1 - Matrix.vecMulVec l c) *ᵥ Z.G (T.orderEmbOfFin hT k) := by rw [hTΛC]
      rw [hB, det_colsSnoc_one_sub_vecMulVec]
    · simp [hT]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
