import CORALean.ContSet.Polygon.Float.Operations.SplitIntoConvexSets
import CORALean.ContSet.VPolytope.Float.Theorems.Convex

/-!
# `Polygon.splitIntoConvexSets` splits the float polygon into convex sets

Each stored piece denotes a convex set (`VPolytope.convex_construct`: the hull of the vertices
plus the error box), and the union of the pieces is what the float polygon denotes, by
definition. Nothing is computed, so this is a statement about the stored float polygon and its
own pieces, not a claim that the float polygon is the real one.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.splitIntoConvexSets_union (P : Polygon 𝕋) :
    (∀ p ∈ Polygon.splitIntoConvexSets P, Convex ℝ (VPolytope.construct p)) ∧
      (⋃ p ∈ Polygon.splitIntoConvexSets P, VPolytope.construct p) = ContSet.construct P :=
  ⟨fun p _ => p.convex_construct, rfl⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
