module

public import CORALean.ContSet.Capsule.Float.Operations.IsDisjoint
public import CORALean.ContSet.Capsule.Float.Theorems.RadiusLe

@[expose] public section

/-!
# `Capsule.isDisjoint` is sound

A `true` answer exhibits a coordinate `i` whose center gap, rounded down, exceeds the sum of the
radii bounds. A common point `x` would be within the first radius of one center and the second of
the other, so by the triangle inequality the Euclidean distance of the centers, which is at least
their gap in coordinate `i`, would be at most the sum. `false` refutes nothing.

## Inputs
* `k` – Newton steps for sqrt
* `C₁` – first capsule
* `C₂` – second capsule

## Hypotheses
* `h` – `isDisjoint` answers true

## Conclusion
* the two capsules are disjoint
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A coordinate is at most the Euclidean norm. -/
theorem Capsule.aux_abs_le_norm₂ (v : Vec ℝ n) (i : Fin n) : |v i| ≤ ‖v‖₂ := by
  refine Real.abs_le_sqrt ?_
  exact Finset.single_le_sum (f := fun j => v j ^ 2) (fun j _ => sq_nonneg (v j))
    (Finset.mem_univ i)


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.isDisjoint_sound (k : ℕ) {C₁ C₂ : Capsule 𝕋 n} (h : C₁.isDisjoint k C₂ = true) :
    Disjoint C₁.construct C₂.construct := by -- --- PROOF ---
  rw [Set.disjoint_left]
  intro x hx₁ hx₂
  -- the two bounding radii, and the coordinate that separates the centers
  have h₁ := Capsule.radius_le k C₁ hx₁
  have h₂ := Capsule.radius_le k C₂ hx₂
  have hR := add_le_addUp (C₁.radius k) (C₂.radius k)
  obtain ⟨i, -, hi⟩ := List.any_eq_true.1 h
  have a₁ := Capsule.aux_abs_le_norm₂ (x - toRealVec C₁.c) i
  have a₂ := Capsule.aux_abs_le_norm₂ (x - toRealVec C₂.c) i
  simp only [Pi.sub_apply, toRealVec] at a₁ a₂
  rcases Bool.or_eq_true_iff.1 hi with hi | hi
  · have := toReal_lt_of_ltStrict hi
    have := subDown_le_sub (C₁.c i) (C₂.c i)
    rw [abs_le] at a₁ a₂
    linarith [a₁.1, a₁.2, a₂.1, a₂.2]
  · have := toReal_lt_of_ltStrict hi
    have := subDown_le_sub (C₂.c i) (C₁.c i)
    rw [abs_le] at a₁ a₂
    linarith [a₁.1, a₁.2, a₂.1, a₂.2]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
