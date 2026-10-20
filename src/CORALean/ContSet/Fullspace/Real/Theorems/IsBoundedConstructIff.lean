module

public import CORALean.ContSet.Fullspace.Real.Fullspace
public import Mathlib.Analysis.InnerProductSpace.Basic

@[expose] public section

/-!
# The full space is bounded exactly in dimension zero

CORA's `isBounded` for the full space is `dim(fs) == 0`: `false` in every positive
dimension, `true` at `0`, where the one point `Vec ℝ 0` has is all there is.

## Inputs
* `F` – full space

## Hypotheses
* none

## Conclusion
* the full space is bounded iff the dimension is zero
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Fullspace.isBounded_construct_iff (F : Fullspace n) : -- --- CONCL ---
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
