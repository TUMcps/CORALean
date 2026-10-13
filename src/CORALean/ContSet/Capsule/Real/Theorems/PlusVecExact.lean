module

public import CORALean.ContSet.Capsule.Real.Operations.PlusVec
public import CORALean.Global.EuclideanNorm

@[expose] public section

/-!
# `Capsule.plusVec` is exactly the translate

Translating the point by `v` and the centre by `v` leave the distance to the segment unchanged.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open CORALean

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Capsule plus vector is exactly the translate. -/
theorem Capsule.plusVec_exact (C : Capsule n) (v : Vec ℝ n) :
    (C.plusVec v).construct = (fun x => x + v) '' C.construct := by -- --- PROOF ---
  have key : ∀ (x : Vec ℝ n) (t : ℝ), (x + v) - (C.c + v + t • C.g) = x - (C.c + t • C.g) := by
    intro x t; abel
  ext y
  constructor
  · rintro ⟨t, ht, hy⟩
    refine ⟨y - v, ⟨t, ht, ?_⟩, by simp⟩
    have hy' : ‖y - (C.c + v + t • C.g)‖₂ ≤ C.r := hy
    have := key (y - v) t
    rw [sub_add_cancel] at this
    change ‖y - v - (C.c + t • C.g)‖₂ ≤ _
    rw [← this]; exact hy'
  · rintro ⟨x, ⟨t, ht, hx⟩, rfl⟩
    refine ⟨t, ht, ?_⟩
    have hx' : ‖x - (C.c + t • C.g)‖₂ ≤ C.r := hx
    change ‖x + v - (C.c + v + t • C.g)‖₂ ≤ _
    rw [key]; exact hx'

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
