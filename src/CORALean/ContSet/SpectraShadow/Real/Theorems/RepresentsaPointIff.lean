module

public import CORALean.ContSet.SpectraShadow.Real.Operations.RepresentsaPoint
public import CORALean.ContSet.SpectraShadow.Real.Theorems.Basic

@[expose] public section

/-!
# `SpectraShadow.representsa_point` is a singleton

A member whose coordinates are the support values exists exactly when the set is a singleton.

## Inputs
* `S` – spectrahedral shadow

## Hypotheses
* none

## Conclusion
* `SpectraShadow.representsa_point` is a singleton
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.representsa_point_iff (S : SpectraShadow (Vec ℝ n)) :
    S.representsa_point ↔ ∃ p, S.construct = {p} := by -- --- PROOF ---
  unfold SpectraShadow.representsa_point
  constructor
  · -- every member is squeezed to `p` coordinate by coordinate
    rintro ⟨p, hp, h⟩
    refine ⟨p, Set.eq_singleton_iff_unique_mem.mpr ⟨hp, fun x hx => ?_⟩⟩
    funext i
    have h1 := (S.le_supportFunc_of_mem (LinearMap.proj i : Vec ℝ n →ₗ[ℝ] ℝ) hx)
    have h2 := (S.le_supportFunc_of_mem (-(LinearMap.proj i : Vec ℝ n →ₗ[ℝ] ℝ)) hx)
    rw [(h i).1] at h1
    rw [(h i).2] at h2
    have h1' : x i ≤ p i := by simpa using h1
    have h2' : -x i ≤ -p i := by simpa using h2
    show x i = p i
    linarith
  · -- the supremum over `{p}` is `p`, from above and from below
    rintro ⟨p, h⟩
    refine ⟨p, by rw [h]; rfl, fun i => ?_⟩
    constructor <;> simp [SpectraShadow.supportFunc, h]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
