import CORALean.ContSet.Zonotope.Real.Operations.ConstrSat
import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact

/-!
# `constrSat` is sound

The image `C Z` is the zonotope `Zonotope.mtimes C Z` (`mtimes_exact`), its box contains it
(`interval_contains`), and a point of the box lies below the box's `supremum`, which `constrSat`
asks to be below `d`. One direction only: the box over-approximates, so `false` says nothing.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.constrSat_sound {Z : Zonotope (Vec ℝ n)} {C : Mat ℝ m n} {d : Vec ℝ m}
    (h : Z.constrSat C d) : ∀ x ∈ Z.construct, ∀ i, (C *ᵥ x) i < d i := by -- --- PROOF ---
  intro x hx i
  have hmem : C *ᵥ x ∈ (Zonotope.mtimes C Z).construct := by
    rw [← Zonotope.mtimes_exact]; exact ⟨x, hx, rfl⟩
  have hle : (C *ᵥ x) i ≤ (Zonotope.mtimes C Z).interval.sup i :=
    ((Zonotope.mtimes C Z).interval_contains hmem i).2
  have := h i
  simp only [Interval.supremum] at this
  linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
