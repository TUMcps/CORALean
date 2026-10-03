import CORALean.ContSet.Taylm.Real.Operations.PolyBounds

/-!
# A polynomial's bounds are at most its coefficients' magnitudes

Each term's bound lies in `[-|a|, |a|]`, every monomial being in `[-1, 1]` on the box, so the
ends of `polyBounds` are at most the sum of the magnitudes.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.abs_polyBounds_le (L : List (ℝ × (Fin n → ℕ))) :
    |(Taylm.polyBounds L).1| ≤ (L.map fun a => |a.1|).sum ∧
      |(Taylm.polyBounds L).2| ≤ (L.map fun a => |a.1|).sum := by -- --- PROOF ---
  induction L with
  | nil => simp [Taylm.polyBounds]
  | cons a L ih =>
    simp only [Taylm.polyBounds, List.map_cons, List.sum_cons] at ih ⊢
    -- one term's bounds, by the three cases of `termBounds`
    have ht : |(Taylm.termBounds a).1| ≤ |a.1| ∧ |(Taylm.termBounds a).2| ≤ |a.1| := by
      unfold Taylm.termBounds
      split_ifs
      · simp
      · constructor
        · rw [abs_le]; constructor
          · exact le_min (neg_abs_le _) (by simp)
          · exact le_trans (min_le_right _ _) (abs_nonneg _)
        · rw [abs_le]; constructor
          · exact le_trans (by simp) (le_max_right _ _)
          · exact max_le (le_abs_self _) (abs_nonneg _)
      · simp
    exact ⟨le_trans (abs_add_le _ _) (add_le_add ht.1 ih.1),
      le_trans (abs_add_le _ _) (add_le_add ht.2 ih.2)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
