import CORALean.ContSet.SpectraShadow.Float.Operations.RepresentsaPoint
import CORALean.ContSet.SpectraShadow.Float.Theorems.ContainsPointSound

/-!
# A `true` from `SpectraShadow.representsa_point` proves a singleton

The set lies in the certified box (`SpectraShadow.interval_contains`), which is the single point
its corner reads as, and that point is a member (`SpectraShadow.containsPoint_sound`).
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.representsa_point_sound {S : SpectraShadow 𝕋 n}
    {Yup Ylo : Fin n → Mat 𝕋 S.k S.k} {β : Vec 𝕋 S.m}
    (h : S.representsa_point Yup Ylo β = true) : ∃ p, S.construct = {p} := by -- --- PROOF ---
  unfold SpectraShadow.representsa_point at h
  split at h
  · rename_i I hI
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_finRange, forall_const] at h
    obtain ⟨hflat, hmem⟩ := h
    refine ⟨toRealVec I.sup, Set.eq_singleton_iff_unique_mem.mpr
      ⟨SpectraShadow.containsPoint_sound hmem, fun x hx => ?_⟩⟩
    -- every member is squeezed between the two equal corners
    have hb := SpectraShadow.interval_contains hI hx
    funext i
    have hi : toReal (I.inf i) ≤ x i ∧ x i ≤ toReal (I.sup i) := hb i
    have e₁ := toReal_le_of_le (hflat i).2
    simp only [toRealVec]
    linarith [hi.1, hi.2]
  · exact absurd h (by simp)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
