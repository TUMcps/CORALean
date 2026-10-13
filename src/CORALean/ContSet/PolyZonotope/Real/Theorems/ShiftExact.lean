import CORALean.ContSet.PolyZonotope.Real.Operations.Shift
import Mathlib.Tactic.Abel

/-!
# `PolyZonotope.shift` is exactly the translate

The centre is the only thing that moves, so the same factors reach `x + v` in both sets.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.shift_exact (pZ : PolyZonotope α) (v : α) :
    (fun x => x + v) '' pZ.construct = (pZ.shift v).construct := by -- --- PROOF ---
  have key : ∀ (a : Fin pZ.p → ℝ) (b : Fin pZ.q → ℝ),
      pZ.c + ∑ i, PolyZonotope.monomial pZ.E a i • pZ.G i + ∑ j, b j • pZ.GI j + v =
        (pZ.shift v).c + ∑ i, PolyZonotope.monomial (pZ.shift v).E a i • (pZ.shift v).G i
          + ∑ j, b j • (pZ.shift v).GI j := by
    intro a b
    show _ = pZ.c + v + ∑ i, PolyZonotope.monomial pZ.E a i • pZ.G i + ∑ j, b j • pZ.GI j
    abel
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨x, ⟨a, b, ha, hb, rfl⟩, rfl⟩
    exact ⟨a, b, ha, hb, key a b⟩
  · rintro y ⟨a, b, ha, hb, rfl⟩
    exact ⟨_, ⟨a, b, ha, hb, rfl⟩, key a b⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
