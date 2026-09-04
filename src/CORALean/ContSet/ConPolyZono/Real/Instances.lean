import CORALean.ContSet.ConPolyZono.Real.Theorems.MapExact
import CORALean.ContSet.ConPolyZono.Real.Theorems.PlusExact

/-!
# What `ConPolyZono` instantiates

`ContSet`, `Plus` and `Mtimes`, each obligation a theorem from `Theorems` read
in the `⊆` direction, and nothing else.

No `ConvexSet`: the sets are generally not convex, which is the point of the
representation. No `CompactSet` either, though they are compact — the argument
wants the constraint set to be closed and bounded and is not written here.

No `LinComb` and no `Reduce`. CORA computes both, and neither is faked: a
`linComb` would have to relax the independent block as `PolyZonotope`'s does,
and order reduction here is not the zonotope's generator ranking — it has to
merge equal exponent columns and drop the factors that fall out of use, in the
constraint matrix as well as in the generators.

`and` and `quadMap` have no class to instantiate, so a caller names
`ConPolyZono.and` and `ConPolyZono.quadMap`. `and` would deserve one most, but
the second implementor, `ConZonotope`, could state it at convex sets only.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   02-September-2026
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α] {n : ℕ}

instance : ContSet (ConPolyZono α) α := ⟨ConPolyZono.construct⟩

instance : Plus (ConPolyZono α) α where
  plus := ConPolyZono.plus
  plus_outer C₁ C₂ := (ConPolyZono.plus_exact C₁ C₂).subset

instance : Mtimes (Mat ℝ) (fun n => ConPolyZono (Vec ℝ n)) where
  mtimes := ConPolyZono.mtimes
  mtimes_outer M C := by
    simp only [ContSet.construct_mat, Scalar.toRealMat_real, Set.biUnion_singleton]
    exact (ConPolyZono.mtimes_exact M C).subset

/-- The constrained-polynomial-zonotope family over vectors. The elaborator
cannot read the family off one member, so a use site names it: `(S := 𝒞𝒫𝒵)`. -/
scoped notation "𝒞𝒫𝒵" => fun n => ConPolyZono (Vec ℝ n)

end CORALean.Real
