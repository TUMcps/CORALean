import CORALean.ContSet.Zoo.Real.Operations.Times
import CORALean.ContSet.Taylm.Real.Theorems.TimesOuter
import CORALean.ContSet.Interval.Real.Theorems.TimesOuter

/-!
# `Zoo.times` encloses

Every member of the result encloses the combined function: the Taylor model by
`Taylm.times_outer`, the interval by `Interval.times_outer` on the two box values.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zoo.times_outer {Z₁ Z₂ : Zoo n} {f g : Vec ℝ n → ℝ} (h₁ : Z₁.Encloses f)
    (h₂ : Z₂.Encloses g) :
    (Z₁.times Z₂).Encloses fun t => f t * g t := by -- --- PROOF ---
  refine ⟨fun T hT => ?_, fun I hI t ht => ?_⟩
  · obtain ⟨a, b, ha, hb, rfl⟩ := Option.map₂_eq_some_iff.1 hT
    exact Taylm.times_outer (h₁.1 a ha) (h₂.1 b hb)
  · obtain ⟨a, b, ha, hb, rfl⟩ := Option.map₂_eq_some_iff.1 hI
    exact Interval.times_outer _ _ ⟨_, h₁.2 a ha t ht, _, h₂.2 b hb t ht, rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
