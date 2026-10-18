module

public import CORALean.ContSet.ContSet.Definitions.ConvexSet
public import CORALean.ContSet.ContSet.Theorems.Basic
public import CORALean.ContSet.StarSet.Real.Operations.OfPoint
public import CORALean.ContSet.StarSet.Real.Theorems.Convex
public import CORALean.ContSet.StarSet.Real.Theorems.LinPredConvex
public import CORALean.ContSet.StarSet.Real.Theorems.Basic

@[expose] public section

/-!
# What `StarSet` instantiates

`ContSet` at every predicate family, `ConvexSet` where the predicate is convex (CORA's `LinPred`
is), and `OfPoint` at CORA's predicate. Nothing else: at `LinPred` a star set is exactly a bounded
polytope, so its operations are the polytope's, reached through `Conversion/`, and what a layer does
to it (the ReLU step) belongs to the layer.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet


-- ========================================  INSTANCES  ========================================= --

instance {P : ℕ → Type} [∀ m, ContSet (P m) (Vec ℝ m)] {n : ℕ} :
    ContSet (StarSet P n) (Vec ℝ n) := ⟨StarSet.construct⟩

instance {m : ℕ} : ConvexSet (StarSet.LinPred m) (Vec ℝ m) := ⟨StarSet.LinPred.convex_construct⟩

instance {P : ℕ → Type} [∀ m, ContSet (P m) (Vec ℝ m)] [∀ m, ConvexSet (P m) (Vec ℝ m)] {n : ℕ} :
    ConvexSet (StarSet P n) (Vec ℝ n) := ⟨StarSet.convex_construct⟩

instance {n : ℕ} : OfPoint (StarSet StarSet.LinPred n) (Vec ℝ n) where
  ofPoint := StarSet.ofPoint
  mem_ofPoint := StarSet.mem_ofPoint

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
