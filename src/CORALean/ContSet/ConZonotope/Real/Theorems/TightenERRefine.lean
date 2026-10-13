import CORALean.ContSet.ConZonotope.Real.Operations.TightenER
import CORALean.Global.FoldInduction

/-!
# Iterating `ConZonotope.tightenER` refines `E`

[2, Alg. 1]: "Algorithm 1 can be applied iteratively to further refine `E`", repeated by
[1, Alg. 1 (iteration)]. Every step of lines 3-5 meets `E_j` and `R_j` with a new bound and never
widens either, so a further pass returns an `E` inside the one it started from, and an `R`
inside its `R`. Together with `tightenER_outer`, which keeps `B∞(A, b)` inside every pass,
that is the refinement: the boxes shrink and stay sound.

## References

* [1] V. Raghuraman and J. P. Koeln. "Set operations and order reductions for
      constrained zonotopes". Automatica, 139:110204, 2022. arXiv:2009.06039.
* [2] J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes:
      A new tool for set-based estimation and fault detection". Automatica, 69:126-136,
      2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `S'` is no wider than `S`, in `E` and in `R`, coordinate by coordinate. -/
def ConZonotope.aux_Tighter {ng : ℕ} (S' S : Interval (Vec ℝ ng) × ((Fin ng → EReal) ×
    (Fin ng → EReal))) : Prop :=
  ∀ j, S.1.inf j ≤ S'.1.inf j ∧ S'.1.sup j ≤ S.1.sup j ∧ S.2.1 j ≤ S'.2.1 j ∧ S'.2.2 j ≤ S.2.2 j

/-- `aux_Tighter` composes. -/
theorem ConZonotope.aux_tighter_trans {ng : ℕ}
    {S'' S' S : Interval (Vec ℝ ng) × ((Fin ng → EReal) × (Fin ng → EReal))}
    (h₁ : ConZonotope.aux_Tighter S'' S') (h₂ : ConZonotope.aux_Tighter S' S) :
    ConZonotope.aux_Tighter S'' S := fun j =>
  ⟨(h₂ j).1.trans (h₁ j).1, (h₁ j).2.1.trans (h₂ j).2.1, (h₂ j).2.2.1.trans (h₁ j).2.2.1,
    (h₁ j).2.2.2.trans (h₂ j).2.2.2⟩

/-- Lines 3-5 only ever meet `E_j` and `R_j` with something. -/
theorem ConZonotope.aux_tightenCoeffER_tighter {nc ng : ℕ} (A : Mat ℝ nc ng) (b : Vec ℝ nc)
    (i : Fin nc) (j : Fin ng)
    (S : Interval (Vec ℝ ng) × ((Fin ng → EReal) × (Fin ng → EReal))) :
    ConZonotope.aux_Tighter (ConZonotope.tightenCoeffER A b i j S) S := by -- --- PROOF ---
  intro k
  unfold ConZonotope.tightenCoeffER
  split_ifs with h0
  · exact ⟨le_rfl, le_rfl, le_rfl, le_rfl⟩
  unfold ConZonotope.tightenCoeff
  rw [if_neg h0]
  rcases eq_or_ne k j with rfl | hk
  · simp only [Function.update_self]
    exact ⟨le_max_left _ _, min_le_left _ _, le_max_left _ _, min_le_left _ _⟩
  · simp only [Function.update_of_ne hk]
    exact ⟨le_rfl, le_rfl, le_rfl, le_rfl⟩

/-- A whole pass of lines 2-10 is no wider than its start. -/
theorem ConZonotope.aux_tightenPassER_tighter {nc ng : ℕ} (A : Mat ℝ nc ng) (b : Vec ℝ nc)
    (S : Interval (Vec ℝ ng) × ((Fin ng → EReal) × (Fin ng → EReal))) :
    ConZonotope.aux_Tighter (ConZonotope.tightenPassER A b S) S := by -- --- PROOF ---
  unfold ConZonotope.tightenPassER
  refine Fin.foldl_induction (P := fun S' => ConZonotope.aux_Tighter S' S) nc _ S
    (fun _ => ⟨le_rfl, le_rfl, le_rfl, le_rfl⟩) ?_
  intro S' i hS'
  exact Fin.foldl_induction (P := fun S'' => ConZonotope.aux_Tighter S'' S) ng _ S' hS'
    fun S'' j hS'' => ConZonotope.aux_tighter_trans
      (ConZonotope.aux_tightenCoeffER_tighter A b i j S'') hS''


-- =======================================  MAIN THEOREM  ======================================= --

/-- [2, Alg. 1]: one more pass of [1, Alg. 1 (iteration)] returns `E` and `R` inside the previous
ones. -/
theorem ConZonotope.tightenER_succ_refine {nc ng : ℕ} (A : Mat ℝ nc ng) (b : Vec ℝ nc)
    (k : ℕ) (j : Fin ng) :
    (ConZonotope.tightenER A b k).1.inf j ≤ (ConZonotope.tightenER A b (k + 1)).1.inf j ∧
      (ConZonotope.tightenER A b (k + 1)).1.sup j ≤ (ConZonotope.tightenER A b k).1.sup j ∧
      (ConZonotope.tightenER A b k).2.1 j ≤ (ConZonotope.tightenER A b (k + 1)).2.1 j ∧
      (ConZonotope.tightenER A b (k + 1)).2.2 j
        ≤ (ConZonotope.tightenER A b k).2.2 j := by
  unfold ConZonotope.tightenER
  dsimp only
  rw [Function.iterate_succ_apply' _ (k + 1)]
  exact ConZonotope.aux_tightenPassER_tighter A b _ j

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
