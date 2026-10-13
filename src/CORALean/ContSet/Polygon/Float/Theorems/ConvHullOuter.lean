import CORALean.ContSet.Polygon.Float.Operations.ConvHull
import CORALean.ContSet.VPolytope.Float.Theorems.ConvHullOuter
import CORALean.ContSet.VPolytope.Float.Theorems.Convex

/-!
# `Polygon.convHull` contains the convex hull of the polygon

The convex hull of the union of the pieces sits inside the stored polytope: by induction on the
list, each step is `VPolytope.convHull_outer` at a piece and the hull of the rest. Not exact, for
the same reason as at two pieces.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem Polygon.aux_convHullOfList_outer :
    ∀ ps : List (VPolytope (Vec 𝕋 2)),
      convexHull ℝ (⋃ p ∈ ps, VPolytope.construct p) ⊆
        (Polygon.convHullOfList ps).construct
  | [] => by simp
  | [p] => by
    simp only [List.mem_singleton, Set.iUnion_iUnion_eq_left]
    exact convexHull_min (fun x hx => hx) (VPolytope.convex_construct p)
  | p :: q :: ps => by
    have hrec := Polygon.aux_convHullOfList_outer (q :: ps)
    refine subset_trans ?_ (VPolytope.convHull_outer p (Polygon.convHullOfList (q :: ps)))
    refine convexHull_mono ?_
    intro x hx
    simp only [Set.mem_iUnion, List.mem_cons, exists_prop] at hx
    obtain ⟨s, hs | hs, hx⟩ := hx
    · subst hs
      exact Or.inl hx
    · refine Or.inr (hrec (subset_convexHull ℝ _ ?_))
      simp only [Set.mem_iUnion, exists_prop]
      exact ⟨s, List.mem_cons.mpr hs, hx⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.convHull_outer (P : Polygon 𝕋) :
    convexHull ℝ (ContSet.construct P) ⊆ (Polygon.convHull P).construct :=
  Polygon.aux_convHullOfList_outer P.sets

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
