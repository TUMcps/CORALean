module

public import CORALean.ContSet.InflatedContSet.InflatedContSet

@[expose] public section

/-!
# Pushing a nominal part and its box through an additive map

The unary counterpart of `plus_subset`. An additive map sends a Minkowski sum to
the sum of the images, so the two parts travel separately: the nominal part may
spill by `D`, and the box must absorb `D` along with its own image.

Additivity suffices; the map is applied to a sum of two sets and nothing else.
-/

-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   ---
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.InflatedContSet

open Pointwise

variable {𝕋 S T N M : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}
variable [ContSet N (Vec ℝ n)] [ContSet M (Vec ℝ m)]
variable [InflatedContSet S N (Vec 𝕋 n) (Vec ℝ n)] [InflatedContSet T M (Vec 𝕋 m) (Vec ℝ m)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem map_subset {s : S} {t : T} {f : Vec ℝ n → Vec ℝ m} {D : Set (Vec ℝ m)}
    (hadd : ∀ x y, f (x + y) = f x + f y)
    (hnominal : f '' nominalSet s ⊆ nominalSet t + D)
    (herror : f '' (I_error s).construct + D ⊆ (I_error t).construct) : -- --- STMT ---
    f '' construct s ⊆ construct t := by -- --- PROOF ---
  rintro _ ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩
  obtain ⟨t₀, ht₀, d, hd, hsum⟩ := hnominal ⟨a, ha, rfl⟩
  refine ⟨t₀, ht₀, f b + d, herror ⟨f b, ⟨b, hb, rfl⟩, d, hd, rfl⟩, ?_⟩
  rw [hadd, ← hsum, add_assoc, add_comm d (f b)]

end CORALean.Float.InflatedContSet


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
