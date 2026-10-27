module

public import CORALean.ContDynamics.LinearSys.Operations.IsCanonicalFormFloat

@[expose] public section

/-!
# A `true` from the float `isCanonicalForm` is a proof

One-sided: when `isCanonicalFormFloat` answers `true`, the real coefficients the floats denote are
in canonical form [1]. `false` says nothing, since `le` is only sound when it answers `true`.

## Inputs
* `sys` – linear system with float coefficients

## Hypotheses
* `h` – the float canonical-form test passes

## Conclusion
* the real system is in canonical form

## References

* [1] `contDynamics/@linearSys/isCanonicalForm.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]

/-- A `true` from the entry test is a proof. -/
private theorem LinearSys.aux_entryIsFloat_sound {a x : 𝕋}
    (h : LinearSys.step_entryIsFloat a x = true) :
    toReal x = toReal a := by
  unfold LinearSys.step_entryIsFloat at h
  rw [Bool.and_eq_true] at h
  exact le_antisymm (toReal_le_of_le h.2) (toReal_le_of_le h.1)

end


-- =======================================  MAIN THEOREM  ======================================= --

/-- One-sided: `true` gives the real system in canonical form. -/
theorem LinearSys.isCanonicalFormFloat_sound {sys : LinearSys 𝕋 n}
    (h : sys.isCanonicalFormFloat = true) : -- --- CONCL ---
    sys.IsCanonicalForm := by -- --- PROOF ---
  unfold LinearSys.isCanonicalFormFloat at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_finRange,
    forall_const] at h
  obtain ⟨⟨⟨⟨⟨⟨hm, hs⟩, hc⟩, hk⟩, hE⟩, hD⟩, hB⟩ := h
  refine ⟨hm, hs, ?_, ?_, ?_, ?_, ?_⟩
  -- each entry test reads its float as the value it was compared with
  · funext i
    exact (LinearSys.aux_entryIsFloat_sound (hc i)).trans toReal_zero
  · funext i
    exact (LinearSys.aux_entryIsFloat_sound (hk i)).trans toReal_zero
  · funext i j
    exact (LinearSys.aux_entryIsFloat_sound (hE i j)).trans toReal_zero
  · funext i j
    exact (LinearSys.aux_entryIsFloat_sound (hD i j)).trans toReal_zero
  · intro i j
    have := LinearSys.aux_entryIsFloat_sound (hB i j)
    by_cases hij : (i : ℕ) = (j : ℕ)
    · rw [if_pos hij] at this ⊢
      exact this.trans toReal_one
    · rw [if_neg hij] at this ⊢
      exact this.trans toReal_zero

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
