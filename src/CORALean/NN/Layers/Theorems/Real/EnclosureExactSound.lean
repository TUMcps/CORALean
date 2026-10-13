module

public import CORALean.NN.Layers.Definitions.Enclosure

@[expose] public section

/-!
# `σ` itself encloses `σ`

ℝ-only, as `Enclosure.exact` is: only ℝ stores `σ`'s values. Both ends are `σ`, and reading ℝ
is the identity, so the bracket is two equalities.
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem enclosure_exact_sound (σ : ℝ → ℝ) : (Enclosure.exact σ).Sound σ :=
  ⟨fun _ => le_rfl, fun _ => le_rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
