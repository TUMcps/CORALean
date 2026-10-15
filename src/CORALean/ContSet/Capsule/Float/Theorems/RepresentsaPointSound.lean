module

public import CORALean.ContSet.Capsule.Float.Operations.RepresentsaPoint
public import CORALean.ContSet.Capsule.Real.Theorems.RepresentsaPointIff

@[expose] public section

/-!
# `Capsule.representsa_point` is sound

`true` makes the nominal generator and radius `0`, so by the exact layer's
`representsa_point_iff` (for `0 < n`) the capsule is the single point, its stored centre.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.representsa_point_sound (hn : 0 < n) {C : Capsule 𝕋 n}
    (h : Capsule.representsa_point C = true) : C.construct = {toRealVec C.c} := by -- --- PROOF ---
  simp only [Capsule.representsa_point, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    forall_const] at h
  obtain ⟨⟨hg, hr₁⟩, hr₂⟩ := h
  refine (CORALean.Real.Capsule.representsa_point_iff hn C.nominal).mpr ⟨?_, ?_⟩
  · funext i
    have := hg i
    show toReal (C.g i) = 0
    exact le_antisymm (by simpa [toReal_zero] using toReal_le_of_le this.1)
      (by simpa [toReal_zero] using toReal_le_of_le this.2)
  · show toReal C.r = 0
    exact le_antisymm (by simpa [toReal_zero] using toReal_le_of_le hr₁)
      (by simpa [toReal_zero] using toReal_le_of_le hr₂)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
