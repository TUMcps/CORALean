import CORALean.ContSet.Zoo.Float.Operations.Plus
import CORALean.ContSet.Taylm.Float.Theorems.PlusOuter
import CORALean.ContSet.Interval.Float.Theorems.PlusOuter

/-!
# `Zoo.plus` encloses

Every member of the result encloses the combined function: the Taylor model by `Taylm.plus_outer`,
the interval by `Interval.plus_outer` on the two box values (outer: the rounding goes outward).
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zoo.plus_outer {Z₁ Z₂ : Zoo 𝕋 n} {f g : Vec ℝ n → ℝ} (h₁ : Z₁.Encloses f)
    (h₂ : Z₂.Encloses g) :
    (Z₁.plus Z₂).Encloses fun t => f t + g t := by -- --- PROOF ---
  refine ⟨fun T hT => ?_, fun I hI t ht => ?_⟩
  · obtain ⟨a, b, ha, hb, rfl⟩ := Option.map₂_eq_some_iff.1 hT
    exact Taylm.plus_outer (h₁.1 a ha) (h₂.1 b hb)
  · obtain ⟨a, b, ha, hb, rfl⟩ := Option.map₂_eq_some_iff.1 hI
    exact Interval.plus_outer _ _ (Set.add_mem_add (h₁.2 a ha t ht) (h₂.2 b hb t ht))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
