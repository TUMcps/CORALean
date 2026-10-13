import CORALean.ContSet.Zonotope.Real.Theorems.VolumeIntersectStripDet
import Mathlib.Analysis.Convex.Function

/-!
# The volume of the intersection bound is convex in the gain

[1, Sec. 6.1 (convexity)]: "`Vol (p̂(λ) ⊕ Ĥ(λ) Bʳ⁺¹)` is a convex function of `λ`. This means that
obtaining the vector `λ` that minimizes the volume of the zonotope is a convex problem." The volume
is a sum of nonnegative multiples of `|1 - cᵀλ|` and of `|det [B_i σλ]|`, which is `|·|` of a
function linear in `λ` (the determinant is linear in its last column), so each term, and the sum,
is convex. The claim that minimising it is a convex *problem* is this convexity on all of `ℝⁿ`; no
optimiser is built.

## References

* [1] T. Alamo, J. M. Bravo and E. F. Camacho. "Guaranteed state estimation by zonotopes".
      Automatica, 41(6):1035-1043, 2005.
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

theorem Zonotope.volume_intersectStrip_convexOn (Z : Zonotope (Vec ℝ (m+1))) (c : Vec ℝ (m+1))
    (σ d : ℝ) :
    ConvexOn ℝ Set.univ (fun l : Vec ℝ (m+1) =>
      (Zonotope.intersectStrip (Matrix.of fun _ j => c j : Mat ℝ 1 (m+1)) (fun _ => σ)
        (fun _ => d) (Matrix.of fun i _ => l i : Mat ℝ (m+1) 1)
        Z).volume.toReal) := by -- --- PROOF ---
  -- the sum of nonnegative multiples of `|1 - cᵀλ|` and of `|det [B σλ]|`, both convex in `λ`
  set A : Finset (Fin Z.h) → ℝ := fun S => if hS : S.card = m + 1 then
    2 ^ (m+1) * |(Matrix.of fun i k => Z.G (S.orderEmbOfFin hS k) i : Mat ℝ (m+1) (m+1)).det|
    else 0 with hA
  set Bd : Finset (Fin Z.h) → Vec ℝ (m+1) → ℝ := fun T x => if hT : T.card = m then
    2 ^ (m+1) * |(colsSnoc (fun k => Z.G (T.orderEmbOfFin hT k)) (σ • x)).det| else 0 with hBd
  have hAnn : ∀ S, 0 ≤ A S := fun S => by
    by_cases hS : S.card = m + 1 <;> simp [hA, hS]
  have hBnn : ∀ T x, 0 ≤ Bd T x := fun T x => by
    by_cases hT : T.card = m <;> simp [hBd, hT]
  -- the volume, with the sums' factors collected
  have hF : ∀ x : Vec ℝ (m+1), (Zonotope.intersectStrip (Matrix.of fun _ j => c j : Mat ℝ 1 (m+1))
      (fun _ => σ) (fun _ => d) (Matrix.of fun i _ => x i : Mat ℝ (m+1) 1) Z).volume.toReal =
      (∑ S, A S) * |1 - c ⬝ᵥ x| + ∑ T, Bd T x := by
    intro x
    rw [Zonotope.volume_intersectStrip_det, ENNReal.toReal_ofReal]
    · congr 1
      · rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun S _ => ?_
        by_cases hS : S.card = m + 1
        · simp only [hA, hS, dif_pos]
          try ring
        · simp [hA, hS]
    · refine add_nonneg (Finset.sum_nonneg fun S _ => ?_) (Finset.sum_nonneg fun T _ => ?_)
      · by_cases hS : S.card = m + 1
        · simp only [hS, dif_pos]; positivity
        · simp [hS]
      · by_cases hT : T.card = m
        · simp only [hT, dif_pos]; positivity
        · simp [hT]
  -- convexity of each of the two kinds of term
  have h1 : ∀ (x y : Vec ℝ (m+1)) (a b : ℝ), 0 ≤ a → 0 ≤ b → a + b = 1 →
      |1 - c ⬝ᵥ (a • x + b • y)| ≤ a * |1 - c ⬝ᵥ x| + b * |1 - c ⬝ᵥ y| := by
    intro x y a b ha hb hab
    have : 1 - c ⬝ᵥ (a • x + b • y) = a * (1 - c ⬝ᵥ x) + b * (1 - c ⬝ᵥ y) := by
      simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
      linear_combination (-1 : ℝ) * hab
    rw [this]
    calc _ ≤ |a * (1 - c ⬝ᵥ x)| + |b * (1 - c ⬝ᵥ y)| := abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
  have h2 : ∀ (T : Finset (Fin Z.h)) (x y : Vec ℝ (m+1)) (a b : ℝ), 0 ≤ a → 0 ≤ b → a + b = 1 →
      Bd T (a • x + b • y) ≤ a * Bd T x + b * Bd T y := by
    intro T x y a b ha hb hab
    -- subsets of the wrong size contribute nothing
    by_cases hT : T.card = m
    · simp only [hBd, hT, dif_pos]
      set B : Fin m → Vec ℝ (m+1) := fun k => Z.G (T.orderEmbOfFin hT k)
      have hupd : ∀ z, colsSnoc B z = (colsSnoc B 0).updateCol (Fin.last m) z := by
        intro z; ext i k
        refine Fin.lastCases ?_ (fun k => ?_) k
        · simp [colsSnoc]
        · simp [colsSnoc, (Fin.castSucc_lt_last k).ne]
      -- the determinant is linear in the last column
      have : (colsSnoc B (σ • (a • x + b • y))).det =
          a * (colsSnoc B (σ • x)).det + b * (colsSnoc B (σ • y)).det := by
        rw [hupd, hupd (σ • x), hupd (σ • y)]
        have e : σ • (a • x + b • y) = a • (σ • x) + b • (σ • y) := by
          ext i; simp; ring
        rw [e, Matrix.det_updateCol_add, Matrix.det_updateCol_smul _ _ a,
          Matrix.det_updateCol_smul _ _ b]
      rw [this]
      -- so `|det|` is convex
      calc 2 ^ (m+1) * |a * (colsSnoc B (σ • x)).det + b * (colsSnoc B (σ • y)).det|
          ≤ 2 ^ (m+1) * (|a * (colsSnoc B (σ • x)).det| + |b * (colsSnoc B (σ • y)).det|) := by
            gcongr; exact abs_add_le _ _
        _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]; ring
    · simp [hBd, hT]
  have hsum : 0 ≤ ∑ S, A S := Finset.sum_nonneg fun S _ => hAnn S
  -- the sum of convex terms with nonnegative weights
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [hF, smul_eq_mul]
  calc (∑ S, A S) * |1 - c ⬝ᵥ (a • x + b • y)| + ∑ T, Bd T (a • x + b • y)
      ≤ (∑ S, A S) * (a * |1 - c ⬝ᵥ x| + b * |1 - c ⬝ᵥ y|) +
        ∑ T, (a * Bd T x + b * Bd T y) :=
        add_le_add (mul_le_mul_of_nonneg_left (h1 x y a b ha hb hab) hsum)
          (Finset.sum_le_sum fun T _ => h2 T x y a b ha hb hab)
    _ = a * ((∑ S, A S) * |1 - c ⬝ᵥ x| + ∑ T, Bd T x) +
        b * ((∑ S, A S) * |1 - c ⬝ᵥ y| + ∑ T, Bd T y) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]; ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
