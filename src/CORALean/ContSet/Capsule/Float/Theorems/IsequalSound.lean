module

public import CORALean.ContSet.Capsule.Float.Operations.Isequal
public import CORALean.ContSet.Capsule.Real.Theorems.IsequalConstruct

@[expose] public section

/-!
# `Capsule.isequal` is sound

`true` is `le` both ways on every field, so the nominal capsules have equal fields and denote the
same set (`Capsule.isequal_construct`). Not complete: `le` is certified one way only.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.isequal_sound {C S : Capsule 𝕋 n} (h : Capsule.isequal C S = true) :
    C.construct = S.construct := by -- --- PROOF ---
  simp only [Capsule.isequal, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    forall_const] at h
  obtain ⟨⟨⟨hc, hg⟩, hr₁⟩, hr₂⟩ := h
  refine CORALean.Real.Capsule.isequal_construct (C := C.nominal) (S := S.nominal) ⟨?_, ?_, ?_⟩
  · funext i
    have := hc i
    exact le_antisymm (toReal_le_of_le this.1) (toReal_le_of_le this.2)
  · funext i
    have := hg i
    exact le_antisymm (toReal_le_of_le this.1) (toReal_le_of_le this.2)
  · exact le_antisymm (toReal_le_of_le hr₁) (toReal_le_of_le hr₂)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
