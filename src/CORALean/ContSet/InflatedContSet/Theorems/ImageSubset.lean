import CORALean.ContSet.InflatedContSet.InflatedContSet

/-!
# Pushing a nominal part and its box through an additive map, each into its own

The case of `map_subset` with nothing to carry between the two parts: the nominal part lands
in the result's nominal part and the box in the result's box. Selecting or padding coordinates
rounds nothing, so it is this case.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.InflatedContSet

open Pointwise

variable {𝕋 S T N M : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}
variable [ContSet N (Vec ℝ n)] [ContSet M (Vec ℝ m)]
variable [InflatedContSet S N 𝕋 n] [InflatedContSet T M 𝕋 m]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The case where the nominal part lands in the result's nominal part and the box in its box,
so nothing is carried between them: selecting or padding coordinates rounds nothing. -/
theorem image_subset {s : S} {t : T} {f : Vec ℝ n → Vec ℝ m}
    (hadd : ∀ x y, f (x + y) = f x + f y)
    (hnominal : f '' nominalSet s ⊆ nominalSet t)
    (herror : f '' (error s).construct ⊆ (error t).construct) :
    f '' construct s ⊆ construct t := by
  rintro _ ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩
  exact ⟨f a, hnominal ⟨a, ha, rfl⟩, f b, herror ⟨b, hb, rfl⟩, (hadd a b).symm⟩

end CORALean.Float.InflatedContSet


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
