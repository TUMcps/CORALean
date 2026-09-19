import CORALean.ContSet.Zonotope.Real.Operations.Shift

/-!
# `Zonotope.shift` moves the set, not merely the representation

`x ∈ (Z.shift w).construct ↔ x + w ∈ Z.construct`: the generators are the same, so the only
change to a member's defining equation is which point it is read from, `Z.c - w` rather than
`Z.c` — the algebra `abel` closes both directions of.
-/

-- Authors:       Tobias Ladner
-- Written:       18-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.mem_shift_iff (Z : Zonotope α) (w x : α) :
    x ∈ (Z.shift w).construct ↔ x + w ∈ Z.construct := by -- --- PROOF ---
  constructor
  · rintro ⟨β, hβ, rfl⟩
    exact ⟨β, hβ, by unfold Zonotope.shift; module⟩
  · rintro ⟨β, hβ, heq⟩
    refine ⟨β, hβ, ?_⟩
    unfold Zonotope.shift
    rw [eq_sub_of_add_eq heq]; module

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
