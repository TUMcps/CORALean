module

public import CORALean.ContSet.ContSet.Definitions.ConvexSet
public import CORALean.ContSet.SpectraShadow.Float.Theorems.LinCombOuter
public import CORALean.ContSet.SpectraShadow.Float.Theorems.MtimesOuter

@[expose] public section

/-!
# What `SpectraShadow` instantiates

`ContSet` is not among them — `InflatedContSet` supplies it, which is what makes
this the same class the exact layer instantiates. Then `ConvexSet` and `Plus`, as
over ℝ, and `Intersection`, which the float layer's tied form makes rounding-free.
`Mtimes` too, by the same tie: `mtimes` never multiplies a stored generator, which would round
a coefficient of a variable the inequality does not bound (`SpectraShadow.lean` says why), but ties
the point to new free variables and multiplies only the error box. And `LinComb`, the convex hull
`convHull_` of the two.

Not `CompactSet`, for the exact layer's reason.

A shadow's fields are function types, so the one an operation returns is a closure
over the one it was given; `plus` therefore materialises, exactly as `Zonotope`'s
does.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ========================================  INSTANCES  ========================================= --

/-- Not the nominal shadow's own convexity read across: the set is that one plus
the error box, and `Convex.add` is what carries the property over the sum. -/
instance {n : ℕ} : ConvexSet (SpectraShadow 𝕋 (Vec 𝕋 n)) (Vec ℝ n) :=
    ⟨SpectraShadow.convex_construct⟩

instance {n : ℕ} : Plus (SpectraShadow 𝕋 (Vec 𝕋 n)) (Vec ℝ n) where
  plus S₁ S₂ := (S₁.plus S₂).materialise
  plus_outer S₁ S₂ := by
    rw [SpectraShadow.materialise_eq]
    exact SpectraShadow.plus_outer S₁ S₂

/-- The point tied to new free variables by equalities, only the error box multiplied: no stored
generator is multiplied, so nothing needs a box that a free variable would escape. -/
instance : Mtimes (Mat 𝕋) (fun n => SpectraShadow 𝕋 (Vec 𝕋 n)) where
  mtimes M S := (S.mtimes M).materialise
  mtimes_outer M S := by
    simp only [ContSet.construct_mat, Set.biUnion_singleton, SpectraShadow.materialise_eq]
    exact SpectraShadow.mtimes_outer M S

/-- Both error boxes absorbed into the inequality, the two points tied to one: nothing rounds. -/
instance {n : ℕ} : Intersection (SpectraShadow 𝕋 (Vec 𝕋 n)) (Vec ℝ n) where
  intersection S₁ S₂ := (S₁.inter S₂).materialise
  intersection_outer S₁ S₂ := by
    rw [SpectraShadow.materialise_eq]
    exact SpectraShadow.inter_outer S₁ S₂

/-- The convex hull of the union, enclosed: the guarantee `enclose` and `or` ask of `linComb`. -/
instance {n : ℕ} : LinComb (SpectraShadow 𝕋 (Vec 𝕋 n)) (Vec ℝ n) where
  linComb S₁ S₂ := S₁.convHull_ S₂
  linComb_outer S₁ S₂ := SpectraShadow.segments_subset_convHull S₁ S₂

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
