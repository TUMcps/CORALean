import CORALean.ContSet.ContSet.Definitions.ConvexSet
import CORALean.ContSet.SpectraShadow.Float.Theorems.API

/-!
# What `SpectraShadow` instantiates

`ContSet` is not among them — `InflatedContSet` supplies it, which is what makes
this the same class the exact layer instantiates. Then `ConvexSet` and `Plus`, as
over ℝ.

No `Mtimes`: the float `mtimes` would round every generator, and a generator's
rounding multiplies a variable the inequality does not bound, so no box holds what
it costs — `SpectraShadow.lean` says why. Not `CompactSet`, for the exact layer's
reason.

A shadow's fields are function types, so the one an operation returns is a closure
over the one it was given; `plus` therefore materialises, exactly as `Zonotope`'s
does.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ========================================  INSTANCES  ========================================= --

/-- Not the nominal shadow's own convexity read across: the set is that one plus
the error box, and `Convex.add` is what carries the property over the sum. -/
instance {n : ℕ} : ConvexSet (SpectraShadow 𝕋 n) (Vec ℝ n) := ⟨SpectraShadow.convex_construct⟩

instance {n : ℕ} : Plus (SpectraShadow 𝕋 n) (Vec ℝ n) where
  plus S₁ S₂ := (S₁.plus S₂).materialise
  plus_outer S₁ S₂ := by
    rw [SpectraShadow.materialise_eq]
    exact SpectraShadow.plus_outer S₁ S₂

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
