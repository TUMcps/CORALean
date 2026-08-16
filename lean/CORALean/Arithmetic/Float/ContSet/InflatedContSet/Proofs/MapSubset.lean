import CORALean.Arithmetic.Float.ContSet.InflatedContSet.API

/-!
# Pushing a nominal part and its box through an additive map

The unary counterpart of `plus_subset`. An additive map sends a Minkowski sum to
the sum of the images, so the nominal part and the box travel separately: the
nominal part may spill by `D`, and the box must absorb `D` together with its own
image.

Only additivity is needed, not linearity — the map is applied to a sum of two
sets and nothing else.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Arithmetic.Float.InflatedContSet.Proofs

open Pointwise

variable {F S T N M : Type} [FloatOps F] [SoundFloatArithmetic F] {n m : ℕ}
variable [Real.ContSet N n] [Real.ContSet M m]
variable [InflatedContSet S N F n] [InflatedContSet T M F m]

theorem map_subset {s : S} {t : T} {f : Vec ℝ n → Vec ℝ m} {D : Set (Vec ℝ m)}
    (hadd : ∀ x y, f (x + y) = f x + f y)
    (hnominal : f '' nominalSet s ⊆ nominalSet t + D)
    (herror : f '' (error s).construct + D ⊆ (error t).construct) :
    f '' construct s ⊆ construct t := by
  rintro _ ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩
  obtain ⟨t₀, ht₀, d, hd, hsum⟩ := hnominal ⟨a, ha, rfl⟩
  refine ⟨t₀, ht₀, f b + d, herror ⟨f b, ⟨b, hb, rfl⟩, d, hd, rfl⟩, ?_⟩
  rw [hadd, ← hsum, add_assoc, add_comm d (f b)]

end CORALean.Arithmetic.Float.InflatedContSet.Proofs
