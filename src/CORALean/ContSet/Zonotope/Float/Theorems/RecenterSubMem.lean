module

public import CORALean.ContSet.Zonotope.Float.Operations.Recenter
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet

@[expose] public section

/-!
# `Zonotope.recenter` holds every point less the stored center

The nominal part keeps its coefficients, the center leaving it exactly, and the
error point stays where it was, inside the widened box.

## Inputs
* `Z` – zonotope
* `y` – point

## Hypotheses
* `hy` – point lies in the zonotope

## Conclusion
* point less the center lies in the recentered zonotope
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.sub_center_mem_recenter {Z : Zonotope (Vec 𝕋 n)} {y : Vec ℝ n}
    (hy : y ∈ Z.construct) : y - toRealVec Z.c ∈ Z.recenter.construct := by -- --- PROOF ---
  obtain ⟨a, ha, e, he, rfl⟩ := hy
  obtain ⟨β, hβ, ha⟩ := Zonotope.mem_nominalSet_iff.mp ha
  refine ⟨a - toRealVec Z.c, Zonotope.mem_nominalSet_iff.mpr ⟨β, hβ, fun i => ?_⟩, e,
    fun i => ?_, sub_add_eq_add_sub _ _ _⟩
  · simp only [Pi.sub_apply, ha i, Zonotope.recenter, toReal_zero, toRealVec, add_sub_cancel_left,
      zero_add]
    rfl
  · obtain ⟨hlo, hhi⟩ := he i
    show toReal (minimum (Z.I_error.inf i) zero) ≤ e i ∧ e i ≤ toReal
        (maximum (Z.I_error.sup i) zero)
    rw [toReal_minimum, toReal_maximum]
    exact ⟨le_trans (min_le_left _ _) hlo, le_trans hhi (le_max_left _ _)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
