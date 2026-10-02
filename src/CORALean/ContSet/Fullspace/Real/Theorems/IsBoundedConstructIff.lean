import CORALean.ContSet.Fullspace.Real.Fullspace
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# The full space is bounded exactly in dimension zero

CORA's `isBounded` for the full space is `dim(fs) == 0`: `false` in every positive
dimension, `true` at `0`, where the one point `Vec ℝ 0` has is all there is.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Fullspace.isBounded_construct_iff (F : Fullspace n) :
    Bornology.IsBounded F.construct ↔ n = 0 := by -- --- PROOF ---
  rw [Fullspace.construct]
  constructor
  · intro h
    by_contra hn
    haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
    exact NormedSpace.unbounded_univ ℝ (Vec ℝ n) h
  · rintro rfl
    exact (Set.toFinite _).isBounded

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
