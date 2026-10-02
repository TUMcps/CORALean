import CORALean.ContSet.LevelSet.Real.Theorems.ForallFinAdd

/-!
# Stacked constraints hold if each block holds

The stacked operator list and value vector of `and_` satisfy every comparison exactly when each
block does.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem LevelSet.forall_append_holds {a b : ℕ} (o₁ : Fin a → CompOp) (o₂ : Fin b → CompOp)
    (v₁ : Fin a → ℝ) (v₂ : Fin b → ℝ) :
    (∀ i, (Fin.append o₁ o₂ i).holds (Fin.append v₁ v₂ i)) ↔
      (∀ i, (o₁ i).holds (v₁ i)) ∧ ∀ j, (o₂ j).holds (v₂ j) := by
  rw [LevelSet.forall_fin_add]
  simp only [Fin.append_left, Fin.append_right]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
