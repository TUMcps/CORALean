import CORALean.ContSet.SpectraShadow.Real.Theorems.ContainsPointZeroIff

/-!
# `SpectraShadow.containsPoint_of_mem`

At any tolerance `tol ≥ 0` the point test never rejects a member of the set.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.containsPoint_of_mem (S : SpectraShadow α) {p : α}
    (hp : p ∈ S.construct) {tol : ℝ} (htol : 0 ≤ tol) : S.containsPoint p tol := by
  obtain ⟨β, s, h1, h2, h3⟩ := (S.containsPoint_zero_iff p).mpr hp
  exact ⟨β, s, h1, fun i => (h2 i).trans htol, h3⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
