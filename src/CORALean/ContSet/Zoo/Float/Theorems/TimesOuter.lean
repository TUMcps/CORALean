module

public import CORALean.ContSet.Zoo.Float.Operations.Basic
public import CORALean.ContSet.Zoo.Float.Theorems.EnclosesIff
public import CORALean.ContSet.Taylm.Float.Theorems.TimesOuter
public import CORALean.ContSet.Interval.Float.Theorems.Basic

@[expose] public section

/-!
# `Zoo.times` encloses

Every member of the result encloses the combined function: the Taylor model by
`Taylm.times_outer`, the interval by `Interval.times_outer` on the two box values (outer: the
rounding goes outward).
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zoo.times_outer {Z₁ Z₂ : Zoo 𝕋 n} {f g : Vec ℝ n → ℝ} (h₁ : Z₁.Encloses f)
    (h₂ : Z₂.Encloses g) :
    (Z₁.times Z₂).Encloses fun t => f t * g t := by -- --- PROOF ---
  rw [Zoo.encloses_iff] at h₁ h₂ ⊢
  refine ⟨fun T hT => ?_, fun I hI t ht => ?_⟩
  · obtain ⟨a, b, ha, hb, rfl⟩ := Option.map₂_eq_some_iff.1 hT
    exact Taylm.times_outer (h₁.1 a ha) (h₂.1 b hb)
  · obtain ⟨a, b, ha, hb, rfl⟩ := Option.map₂_eq_some_iff.1 hI
    exact Interval.times_outer _ _ ⟨_, h₁.2 a ha t ht, _, h₂.2 b hb t ht, rfl⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
