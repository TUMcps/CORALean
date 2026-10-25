module

public import CORALean.ContSet.Taylm.Real.Operations.Plus
public import CORALean.ContSet.Taylm.Real.Theorems.Basic

@[expose] public section

/-!
# `Taylm.plus` keeps the `(n+1)`-st order scaling

[1, Thm. 1], eq. (2.8) for the sum: the weights add and so do the remainders, so two models
scaled by `C₁` and `C₂` at the same order give one scaled by `C₁ + C₂`, at every `h`.

## Inputs
* `T₁` – first model
* `T₂` – second model
* `h` – domain radius
* `C₁` – first scaling constant
* `C₂` – second scaling constant

## Hypotheses
* `hN` – the models have the same order
* `h₁` – first model is scaled by its constant
* `h₂` – second model is scaled by its constant

## Conclusion
* the sum is scaled by the sum of the constants

## References

* [1] K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion
      Methods". International Journal of Pure and Applied Mathematics, 4(4):379-452, 2003.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.plus_scaled {T₁ T₂ : Taylm n} {h C₁ C₂ : ℝ} (hN : T₁.maxOrder = T₂.maxOrder)
    (h₁ : T₁.IsScaled h C₁) (h₂ : T₂.IsScaled h C₂) : -- --- CONCL ---
    (T₁.plus T₂).IsScaled h (C₁ + C₂) := by -- --- PROOF ---
  obtain ⟨w₁, i₁, s₁⟩ := h₁
  obtain ⟨w₂, i₂, s₂⟩ := h₂
  simp only [Taylm.IsScaled, Taylm.plus, hN, max_self, Taylm.weight_append, add_mul] at *
  exact ⟨add_le_add w₁ w₂, le_trans (abs_add_le _ _) (add_le_add i₁ i₂),
    le_trans (abs_add_le _ _) (add_le_add s₁ s₂)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
