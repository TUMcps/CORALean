module

public import CORALean.ContSet.ConPolyZono.Real.Theorems.MemRelaxIff
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.MemConstructIffOfEq

@[expose] public section

/-!
# Relaxing by no slack loses nothing

`relax` at the slack `0` denotes the set itself: a row met within `|0|` is a row met, and the
slack factors, read by no generator, are then `0` too. What a float set whose rows record no
rounding reads as.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Relaxed by the slack `0`, a set denotes itself. -/
theorem ConPolyZono.relax_zero_construct (cPZ : ConPolyZono α) :
    (cPZ.relax 0).construct = cPZ.construct := by -- --- PROOF ---
  ext x
  rw [ConPolyZono.mem_relax_iff]
  constructor
  · rintro ⟨a, β, ha, hβ, hs, hx⟩
    refine ⟨a, β, ha, hβ, (PolyLevelSet.mem_construct_iff_of_eq cPZ.cons_eq).mpr fun i => ?_, hx⟩
    have h := hs i
    rw [Pi.zero_apply, abs_zero] at h
    exact sub_eq_zero.mp (abs_nonpos_iff.mp h)
  · rintro ⟨a, β, ha, hβ, hs, hx⟩
    refine ⟨a, β, ha, hβ, fun i => ?_, hx⟩
    rw [(PolyLevelSet.mem_construct_iff_of_eq cPZ.cons_eq).mp hs i, sub_self, abs_zero]
    exact abs_nonneg _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
