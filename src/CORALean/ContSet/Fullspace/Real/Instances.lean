import CORALean.ContSet.ContSet.ConvexSet
import CORALean.ContSet.Fullspace.Real.Theorems.API

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

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


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
  centre _ := 0
  recentre _ := ⟨⟩
  zero_mem_recentre _ := Set.mem_univ 0
  sub_centre_mem_recentre _ := Set.mem_univ _

instance : Mtimes (Mat ℝ) (fun n => Fullspace n) where
  mtimes _ _ := ⟨⟩
  mtimes_outer _ _ := fun x _ => Set.mem_univ x

instance : Reindex (fun n => Fullspace n) where
  reindex _ _ := ⟨⟩
  reindex_exact e F := Fullspace.reindexLin_exact e F

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
