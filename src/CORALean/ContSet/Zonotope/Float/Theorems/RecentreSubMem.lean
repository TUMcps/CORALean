import CORALean.ContSet.Zonotope.Float.Operations.Recentre
import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet

/-!
# `Zonotope.recentre` holds every point less the stored centre

The nominal part keeps its coefficients, the centre leaving it exactly, and the
error point stays where it was, inside the widened box.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.sub_centre_mem_recentre {Z : Zonotope 𝕋 n} {y : Vec ℝ n}
    (hy : y ∈ Z.construct) : y - toRealVec Z.c ∈ Z.recentre.construct := by -- --- PROOF ---
  obtain ⟨a, ha, e, he, rfl⟩ := hy
  obtain ⟨β, hβ, ha⟩ := Zonotope.mem_nominalSet_iff.mp ha
  refine ⟨a - toRealVec Z.c, Zonotope.mem_nominalSet_iff.mpr ⟨β, hβ, fun i => ?_⟩, e,
    fun i => ?_, sub_add_eq_add_sub _ _ _⟩
  · simp only [Pi.sub_apply, ha i, Zonotope.recentre, toReal_zero, toRealVec, add_sub_cancel_left,
      zero_add]
    rfl
  · obtain ⟨hlo, hhi⟩ := he i
    show toReal (minimum (Z.E.inf i) zero) ≤ e i ∧ e i ≤ toReal (maximum (Z.E.sup i) zero)
    rw [toReal_minimum, toReal_maximum]
    exact ⟨le_trans (min_le_left _ _) hlo, le_trans hhi (le_max_left _ _)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
