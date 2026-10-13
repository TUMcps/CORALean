module

public import CORALean.ContSet.ConPolyZono.Real.Operations.Empty

@[expose] public section

/-!
# `ConPolyZono.empty` denotes the empty set

The one constraint row asks `1 ≤ (A μ)₀ ≤ 0`, which no value satisfies.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.empty_exact (n : ℕ) : (ConPolyZono.empty n).construct = ∅ := by -- --- PROOF ---
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨a, β, -, -, hsat, -⟩
  obtain ⟨h₁, h₂⟩ := hsat (0 : Fin 1)
  exact absurd (h₁.trans h₂) (by simp [ConPolyZono.empty])

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
