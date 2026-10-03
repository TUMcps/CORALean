import CORALean.ContSet.Capsule.Float.Operations.RepresentsaOrigin
import CORALean.ContSet.Capsule.Float.Theorems.RepresentsaPointSound
import CORALean.ContSet.Capsule.Real.Theorems.RepresentsaOriginIff

/-!
# `Capsule.representsa_origin` is sound

`true` makes the nominal capsule a point with centre `0`, so by the exact layer's
`representsa_origin_iff` (for `0 < n`) it is `{0}`.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.representsa_origin_sound (hn : 0 < n) {C : Capsule 𝕋 n}
    (h : Capsule.representsa_origin C = true) : C.construct = {0} := by -- --- PROOF ---
  simp only [Capsule.representsa_origin, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    forall_const] at h
  obtain ⟨hc, hp⟩ := h
  have hpt : C.nominal.representsa_point := by
    have := Capsule.representsa_point_sound hn hp
    exact (CORALean.Real.Capsule.representsa_point_iff hn C.nominal).mp this
  refine (CORALean.Real.Capsule.representsa_origin_iff hn C.nominal).mpr ⟨?_, hpt⟩
  funext i
  have := hc i
  show toReal (C.c i) = 0
  exact le_antisymm (by simpa [toReal_zero] using toReal_le_of_le this.1)
    (by simpa [toReal_zero] using toReal_le_of_le this.2)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
