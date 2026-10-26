module

public import CORALean.ContSet.Capsule.Float.Operations.RepresentsaPoint
public import CORALean.ContSet.Capsule.Real.Operations.RepresentsaPoint
public import CORALean.ContSet.Interval.Float.Theorems.Basic

@[expose] public section

/-!
# What `Capsule.representsa_point` certifies

A `true` answer certifies, each comparison with `zero` both ways by `le`, that both ends of the
error box are `0` in every coordinate, so the box is the origin, and that the nominal generator and
radius are `0`, the exact layer's `representsa_point`.

## Inputs
* `C` – capsule

## Hypotheses
* `h` – `representsa_point` answers true

## Conclusion
* the error box is the origin and the nominal capsule a point
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Both ends `0` in every coordinate, each certified both ways: the box is the origin. -/
private theorem Capsule.aux_error_eq_origin {C : Capsule 𝕋 n}
    (h : ∀ i, ((le (C.I_error.inf i) zero = true ∧ le zero (C.I_error.inf i) = true) ∧
      le (C.I_error.sup i) zero = true) ∧ le zero (C.I_error.sup i) = true) : -- --- CONCL ---
    C.I_error.construct = {0} := by -- --- PROOF ---
  ext x
  rw [Set.mem_singleton_iff]
  have hb : ∀ i, toReal (C.I_error.inf i) = 0 ∧ toReal (C.I_error.sup i) = 0 := fun i => by
    obtain ⟨⟨⟨a, b⟩, c⟩, d⟩ := h i
    have a' := toReal_le_of_le a; have b' := toReal_le_of_le b
    have c' := toReal_le_of_le c; have d' := toReal_le_of_le d
    rw [toReal_zero] at a' b' c' d'
    exact ⟨le_antisymm a' b', le_antisymm c' d'⟩
  constructor
  · intro hx
    funext i
    have hx' := Interval.mem_vec_iff.mp hx i
    show x i = 0
    linarith [hx'.1, hx'.2, (hb i).1, (hb i).2]
  · rintro rfl
    exact Interval.mem_vec_iff.mpr fun i => ⟨le_of_eq (hb i).1, le_of_eq (hb i).2.symm⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- What `true` certifies: the box is the origin, and the nominal capsule a point. -/
theorem Capsule.representsa_point_parts {C : Capsule 𝕋 n}
    (h : Capsule.representsa_point C = true) : -- --- CONCL ---
    C.I_error.construct = {0} ∧ Real.Capsule.representsa_point C.nominal := by -- --- PROOF ---
  simp only [Capsule.representsa_point, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    forall_const] at h
  obtain ⟨⟨⟨hg, hr₁⟩, hr₂⟩, hI⟩ := h
  refine ⟨Capsule.aux_error_eq_origin hI, ?_, ?_⟩
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
