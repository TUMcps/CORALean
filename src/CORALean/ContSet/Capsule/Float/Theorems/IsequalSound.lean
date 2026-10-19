module

public import CORALean.ContSet.Capsule.Float.Operations.Isequal
public import CORALean.ContSet.Capsule.Real.Theorems.IsequalConstruct
public import CORALean.ContSet.Interval.Float.Theorems.Basic

@[expose] public section

/-!
# `Capsule.isequal` is sound

`true` is `le` both ways on every field, so the nominal capsules have equal fields and denote the
same set (`Capsule.isequal_construct`). Not complete: `le` is certified one way only.

## Inputs
* `C` – first capsule
* `S` – second capsule

## Hypotheses
* `h` – `isequal` answers true

## Conclusion
* the two capsules denote the same set
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.isequal_sound {C S : Capsule 𝕋 n} (h : Capsule.isequal C S = true) :
    C.construct = S.construct := by -- --- PROOF ---
  simp only [Capsule.isequal, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    forall_const] at h
  obtain ⟨⟨⟨⟨hc, hg⟩, hr₁⟩, hr₂⟩, hI⟩ := h
  have hnom : C.nominal.construct = S.nominal.construct := by
    refine CORALean.Real.Capsule.isequal_construct (C := C.nominal) (S := S.nominal) ⟨?_, ?_, ?_⟩
    · funext i
      have := hc i
      exact le_antisymm (toReal_le_of_le this.1) (toReal_le_of_le this.2)
    · funext i
      have := hg i
      exact le_antisymm (toReal_le_of_le this.1) (toReal_le_of_le this.2)
    · exact le_antisymm (toReal_le_of_le hr₁) (toReal_le_of_le hr₂)
  -- the boxes have the same ends
  have hbox : C.I_error.construct = S.I_error.construct := by
    ext x
    rw [Interval.mem_vec_iff, Interval.mem_vec_iff]
    refine forall_congr' fun i => ?_
    obtain ⟨⟨⟨a, b⟩, c⟩, d⟩ := hI i
    rw [le_antisymm (toReal_le_of_le a) (toReal_le_of_le b),
      le_antisymm (toReal_le_of_le c) (toReal_le_of_le d)]
  show InflatedContSet.nominalSet C + C.I_error.construct
    = InflatedContSet.nominalSet S + S.I_error.construct
  rw [hbox]
  exact congrArg (· + _) hnom

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
