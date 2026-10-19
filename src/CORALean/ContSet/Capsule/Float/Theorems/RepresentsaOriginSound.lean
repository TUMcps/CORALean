module

public import CORALean.ContSet.Capsule.Float.Operations.Basic
public import CORALean.ContSet.Capsule.Float.Theorems.RepresentsaPointSound
public import CORALean.ContSet.Capsule.Real.Theorems.RepresentsaOriginIff

@[expose] public section

/-!
# `Capsule.representsa_origin` is sound

`true` makes the capsule its stored center (`representsa_point_sound`, for `0 < n`), and that
center `0`.

## Inputs
* `C` – capsule

## Hypotheses
* `hn` – dimension positive
* `h` – `representsa_origin` answers true

## Conclusion
* the capsule denotes the singleton origin
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


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
  rw [Capsule.representsa_point_sound hn hp]
  refine congrArg _ (funext fun i => ?_)
  have := hc i
  show toReal (C.c i) = 0
  exact le_antisymm (by simpa [toReal_zero] using toReal_le_of_le this.1)
    (by simpa [toReal_zero] using toReal_le_of_le this.2)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
