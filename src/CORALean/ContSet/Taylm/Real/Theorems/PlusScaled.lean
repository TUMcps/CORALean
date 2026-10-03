import CORALean.ContSet.Taylm.Real.Operations.Plus
import CORALean.ContSet.Taylm.Real.Theorems.WeightAppend

/-!
# `Taylm.plus` keeps the `(n+1)`-st order scaling

[1, Thm. 1], eq. (2.8) for the sum: the weights add and so do the remainders, so two models
scaled by `C₁` and `C₂` at the same order give one scaled by `C₁ + C₂`, at every `h`.

## References

* [1] K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion
      Methods". International Journal of Pure and Applied Mathematics, 4(4):379-452, 2003.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.plus_scaled {T₁ T₂ : Taylm n} {h C₁ C₂ : ℝ} (hN : T₁.maxOrder = T₂.maxOrder)
    (h₁ : T₁.Scaled h C₁) (h₂ : T₂.Scaled h C₂) :
    (T₁.plus T₂).Scaled h (C₁ + C₂) := by -- --- PROOF ---
  obtain ⟨w₁, i₁, s₁⟩ := h₁
  obtain ⟨w₂, i₂, s₂⟩ := h₂
  simp only [Taylm.Scaled, Taylm.plus, hN, max_self, Taylm.weight_append, add_mul] at *
  exact ⟨add_le_add w₁ w₂, le_trans (abs_add_le _ _) (add_le_add i₁ i₂),
    le_trans (abs_add_le _ _) (add_le_add s₁ s₂)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
