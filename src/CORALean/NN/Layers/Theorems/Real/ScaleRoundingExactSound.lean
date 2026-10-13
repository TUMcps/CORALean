module

public import CORALean.NN.Layers.Definitions.ScaleRounding

@[expose] public section

/-!
# Multiplication by `r` rounds multiplication by `r`

ℝ-only, as `ScaleRounding.exact` is: only ℝ stores `r · x` exactly. Both directions are the
product itself.
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem scaleRounding_exact_sound (r : ℝ) : (ScaleRounding.exact r).Sound r :=
  ⟨fun _ => le_rfl, fun _ => le_rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
