module

public import CORALean.ContSet.ConPolyZono.Real.Operations.Empty
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.MemConstructIffOfEq

@[expose] public section

/-!
# `ConPolyZono.empty` denotes the empty set

The one constraint row asks `(A μ)₀ = 1` of an empty matrix, whose product is `0`.
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
  have h := (PolyLevelSet.mem_construct_iff_of_eq (ConPolyZono.empty n).cons_eq).mp hsat
    (0 : Fin 1)
  simp [ConPolyZono.empty, Matrix.mulVec] at h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
