import CORALean.ContSet.ContSet.Definitions.ConvexSet
import CORALean.ContSet.Fullspace.Real.Operations.Centre
import CORALean.ContSet.Fullspace.Real.Theorems.ReindexLinExact
import CORALean.ContSet.WithEmpty.WithEmpty

/-!
# What `Fullspace` instantiates

Everything whose obligation `Set.univ` on the right meets, which is every class
here bar one: convexity, a sum, a combination, a difference, a reduction, a
product and a point all land in the whole space, and `Recentre` has the origin
to hand as well.

No `CompactSet`: the whole of `Vec ℝ n` is unbounded at `0 < n`, so the class's
unconditional obligation is false. `ZonoBundle` refuses it for the same reason,
an empty family of zonotopes denoting `Set.univ` too.

`Reindex` is the one that needs an argument, `reindexLin_exact`, because its
obligation is an equality and the image of everything has to be shown to be
everything again.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix Pointwise

variable {n : ℕ}


-- ========================================  INSTANCES  ========================================= --

instance : ContSet (Fullspace n) (Vec ℝ n) := ⟨Fullspace.construct⟩

instance : ConvexSet (Fullspace n) (Vec ℝ n) := ⟨fun _ => convex_univ⟩

/-- Each obligation below ends in `Set.mem_univ`: the result is the whole
space, so whatever the operands hold is already in it. -/
instance : Plus (Fullspace n) (Vec ℝ n) where
  plus _ _ := ⟨⟩
  plus_outer _ _ := fun x _ => Set.mem_univ x

instance : LinComb (Fullspace n) (Vec ℝ n) where
  linComb _ _ := ⟨⟩
  linComb_outer _ _ := fun x _ => Set.mem_univ x

instance : MinkDiff (Fullspace n) (Vec ℝ n) where
  minkDiff _ _ := ⟨⟩
  minkDiff_inner _ _ := fun _ _ _ _ => Set.mem_univ _

instance : Reduce (Fullspace n) (Vec ℝ n) where
  reduce F _ := F
  reduce_outer _ _ := fun x _ => Set.mem_univ x

instance : OfPoint (Fullspace n) (Vec ℝ n) where
  ofPoint _ := ⟨⟩
  mem_ofPoint v := Set.mem_univ v

/-- Centred at the origin, which recentring then leaves where it is. -/
instance : Recentre (Fullspace n) (Vec ℝ n) where
  centre := Fullspace.centre
  recentre _ := ⟨⟩
  zero_mem_recentre _ := Set.mem_univ 0
  sub_centre_mem_recentre _ := Set.mem_univ _

/-- At every scalar `𝕋` with a matrix denotation (`Mat 𝕋`), not only `ℝ`: the guarantee
is over what the matrix denotes, and the result ignores it. -/
instance {𝕋 : Type} [Scalar 𝕋] : Mtimes (Mat 𝕋) (fun n => Fullspace n) where
  mtimes _ _ := ⟨⟩
  mtimes_outer _ _ := fun x _ => Set.mem_univ x

/-- CORA's `contains_` answers `true` for every operand (and throws at `R^0`, which
nothing here does): everything is in the whole space. -/
instance {S : Type} [ContSet S (Vec ℝ n)] : Contains (Fullspace n) S where
  contains _ _ := true
  contains_sound _ _ _ := Set.subset_univ _

/-- CORA's `isIntersecting_` answers `~isemptyobject(S)`: the whole space meets every nonempty set.
The wrapper `WithEmpty` is the representation that can say it: disjoint (`true`) exactly at its own
`empty` member; an `of s` answers `false`, which refutes nothing (`s` may denote `∅`). -/
instance {S : Type} [ContSet S (Vec ℝ n)] : IsDisjoint (Fullspace n) (WithEmpty S) where
  isDisjoint _ s := match s with
    | .empty => true
    | .of _ => false
  isDisjoint_sound _ s h := by
    cases s with
    | empty => exact Set.empty_disjoint _
    | of s => exact absurd h (by simp)

instance : Reindex (fun n => Fullspace n) where
  reindex _ _ := ⟨⟩
  reindex_exact e F := Fullspace.reindexLin_exact e F

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
