import CORALean.Global.BlockDiag
import CORALean.ContSet.SpectraShadow.Real.Operations.Plus

/-!
# The inequality of a sum is the two inequalities

At the appended fields rather than at `plus`, so that every dimension is a plain
sum and `simp` reads the entries: the first block of the combination is the first
set's inequality at the first half of the variables, the second the second's at the
second half, and the off-diagonal blocks vanish.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.lmi_append {k₁ k₂ m₁ m₂ : ℕ} (A₀ : Mat ℝ k₁ k₁) (B₀ : Mat ℝ k₂ k₂)
    (A : Fin m₁ → Mat ℝ k₁ k₁) (B : Fin m₂ → Mat ℝ k₂ k₂) (β : Fin (m₁ + m₂) → ℝ) :
    blockDiag 0 A₀ B₀ + ∑ i, β i • (Fin.append (fun i => blockDiag 0 (A i) 0)
        (fun j => blockDiag 0 0 (B j)) : Fin (m₁ + m₂) → Mat ℝ (k₁ + k₂) (k₁ + k₂)) i
      = blockDiag 0 (A₀ + ∑ i, β (Fin.castAdd m₂ i) • A i)
          (B₀ + ∑ j, β (Fin.natAdd m₁ j) • B j) := by
  rw [Fin.sum_univ_add]
  refine blockDiag_ext ?_ ?_ ?_ ?_ <;> intros <;> simp [Matrix.sum_apply]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
