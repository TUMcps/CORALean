module

public import CORALean.ContDynamics.Conform.Definitions.ZonoConformal

@[expose] public section

/-!
# The prediction set of a zono-conformal predictor is a zonotope

[1, Lemma 3]: inserting `U = ⟨0, G_u diag(α)⟩` into (13) gives
`Y_ZCP(x) = ⟨f(x), D̄(x) G_u diag(α)⟩`, the generators of `U` mapped by `D̄(x)`. An equality
of sets, for any `α`.

## Inputs
* `fx` – prediction at the point
* `D` – derivative in the uncertainties
* `Gu` – uncertainty generators
* `α` – generator scaling

## Hypotheses
* none

## Conclusion
* the prediction set equals a stretched template zonotope

## References

* [1] [L. Lützow, M. Eichelbeck, M. J. Kochenderfer and M. Althoff. "Zono-Conformal Prediction:
      Zonotope-Based Uncertainty Quantification for Regression and Classification Tasks". Journal of
      Machine Learning Research,
      2025.](../../../../../references/2025/luetzow-jmlr-zono-conformal-prediction.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {ny nu : ℕ} {ι : Type} [Fintype ι]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Lemma 3]: `Y_ZCP(x) = ⟨f(x), D̄(x) G_u diag(α)⟩`. -/
theorem Conform.zcpSet_eq (fx : Vec ℝ ny) (D : Mat ℝ ny nu) (Gu : ι → Vec ℝ nu)
    (α : ι → ℝ) : -- --- CONCL ---
    Conform.zcpSet fx D Gu α = Conform.templateZono fx (fun j => D *ᵥ Gu j) α := by -- --- PROOF ---
  ext y
  constructor
  · rintro ⟨_, ⟨β, hβ, rfl⟩, rfl⟩
    exact ⟨β, hβ, by simp only [zero_add, mulVec_sum, mulVec_smul]⟩
  · rintro ⟨β, hβ, rfl⟩
    exact ⟨_, ⟨β, hβ, rfl⟩, by simp only [zero_add, mulVec_sum, mulVec_smul]⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
