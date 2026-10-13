module

public import CORALean.ContSet.Capsule.Real.Capsule

@[expose] public section

/-!
# A capsule with a negative radius is empty

`Real.sqrt` never returns a negative value, so no `x` can meet the bound at
`C.r < 0`. Shared by `Convex.lean` and `IsCompact.lean`, both of which split on
the sign of `C.r`.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.construct_eq_empty {C : Capsule n} (hr : C.r < 0) : C.construct = ∅ := by
  ext x
  simp only [Capsule.construct, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨t, -, hle⟩
  linarith [Real.sqrt_nonneg (∑ i, (x i - (C.c i + t * C.g i)) ^ 2)]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
