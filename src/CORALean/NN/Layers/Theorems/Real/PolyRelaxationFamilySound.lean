module

public import CORALean.NN.Layers.Definitions.PolyFamily

@[expose] public section

/-!
# The family is sound at every level

ℝ-only, as the family is: each level is a sampled relaxation, sound at every box.

## Inputs
* `σ` – activation function
* `σ'` – its derivative
* `Mσ` – bound on the derivative

## Hypotheses
* `hd` – the activation has the given derivative
* `hσ` – the derivative is bounded

## Conclusion
* the family is sound at every level
-/

-- Authors:       Claude Opus 5.5
-- Written:       05-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem polyRelaxationFamily_sound {σ σ' : ℝ → ℝ} {Mσ : ℝ}
    (hd : ∀ x, HasDerivAt σ (σ' x) x) (hσ : ∀ x, |σ' x| ≤ Mσ) :
    (polyRelaxationFamily hd hσ).IsSound σ :=
  ⟨fun o => (exists_polyRelaxation_error_lt (L := -(o : ℝ)) (U := (o : ℝ)) hd hσ
    (show (0 : ℝ) < 1 / ((o : ℝ) + 1) by positivity)).choose_spec.choose_spec.1⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
