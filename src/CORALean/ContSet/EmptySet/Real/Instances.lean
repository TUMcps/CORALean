import CORALean.ContSet.ContSet.Definitions.CompactSet
import CORALean.ContSet.ContSet.Definitions.ConvexSet
import CORALean.ContSet.EmptySet.Real.EmptySet

/-!
# What `EmptySet` instantiates

Everything whose obligation a subset of `∅` can meet, which is every class here
that does not ask for a point: `∅` is convex and compact, and it is its own
sum, combination, difference, reduction, image and relabelling — the last one
exactly, `Reindex`'s obligation being the only equality among them.

`Mtimes` and `Reindex` take the family `fun n => EmptySet n`, which is what
lets an algorithm that changes dimension carry an empty set along.

No `OfPoint` and no `Recentre`: each asks for a point of the set — a named one
in the first case, the origin after recentring in the second — and this
representation has none to give.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix Pointwise

variable {n : ℕ}


-- ========================================  INSTANCES  ========================================= --

instance : ContSet (EmptySet n) (Vec ℝ n) := ⟨EmptySet.construct⟩

instance : ConvexSet (EmptySet n) (Vec ℝ n) := ⟨fun _ => convex_empty⟩

instance : CompactSet (EmptySet n) (Vec ℝ n) := ⟨fun _ => isCompact_empty⟩

/-- Each of the four below reads the same way: a point of the result would need
a point of an operand, and `hx.elim` is that nothing is one. -/
instance : Plus (EmptySet n) (Vec ℝ n) where
  plus _ _ := ⟨⟩
  plus_outer _ _ := by rintro x ⟨a, ha, -⟩; exact ha.elim

instance : LinComb (EmptySet n) (Vec ℝ n) where
  linComb _ _ := ⟨⟩
  linComb_outer _ _ := by rintro x ⟨a, ha, -⟩; exact ha.elim

instance : MinkDiff (EmptySet n) (Vec ℝ n) where
  minkDiff _ _ := ⟨⟩
  minkDiff_inner _ _ := by intro x hx; exact hx.elim

instance : Reduce (EmptySet n) (Vec ℝ n) where
  reduce E _ := E
  reduce_outer _ _ := by intro x hx; exact hx.elim

instance : Mtimes (Mat ℝ) (fun n => EmptySet n) where
  mtimes _ _ := ⟨⟩
  mtimes_outer _ _ := by
    -- the union is over images of `∅`, so a member of it holds a member of `∅`
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨-, -, y, hy, -⟩ := hx
    exact hy.elim

/-- CORA's `isIntersecting_` answers `false` outright, so nothing is ever shared with
the empty set and `true` is the right answer for every operand. -/
instance {S : Type} [ContSet S (Vec ℝ n)] : IsDisjoint (EmptySet n) S where
  isDisjoint _ _ := true
  isDisjoint_sound _ _ _ := Set.disjoint_empty _

/-- Exact, not merely outer: relabelling `∅` is `∅` by `Set.image_empty`. -/
instance : Reindex (fun n => EmptySet n) where
  reindex _ _ := ⟨⟩
  reindex_exact _ _ := (Set.image_empty _).symm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
