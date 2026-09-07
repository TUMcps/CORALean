import CORALean.ContSet.ContSet.CompactSet
import CORALean.ContSet.ContSet.ConvexSet
import CORALean.ContSet.Interval.Real.Instances
import CORALean.ContSet.ConZonotope.Real.Theorems.AndExact
import CORALean.ContSet.ConZonotope.Real.Theorems.Convex
import CORALean.ContSet.ConZonotope.Real.Theorems.IsCompact
import CORALean.ContSet.ConZonotope.Real.Theorems.LinCombOuter
import CORALean.ContSet.ConZonotope.Real.Theorems.MapExact
import CORALean.ContSet.ConZonotope.Real.Theorems.MtimesExact
import CORALean.ContSet.ConZonotope.Real.Theorems.MtimesIntervalMatOuter
import CORALean.ContSet.ConZonotope.Real.Theorems.OfPointMem
import CORALean.ContSet.ConZonotope.Real.Theorems.PlusExact
import CORALean.ContSet.ConZonotope.Real.Theorems.ReduceOuter

/-!
# What `ConZonotope` instantiates

Noncomputable, as `reduce` is: it ranks generators, and ordering reals cannot be
computed.

`And` from `and_exact` read in the `⊆` direction: two constrained zonotopes
intersect to one exactly, which is the whole reason the representation exists.

`OfPoint` at no generators and no constraints, `HPolytope.fullspace` standing
in for the empty polytope — the singleton the jump reset asks any
representation to build, one `OfInterval` cheaper.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   07-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- ========================================  INSTANCES  ========================================= --

/-- At every ambient type, not only `Vec`: the constraints live on the
coefficient space whatever the generators point into. -/
instance {α : Type} [AddCommGroup α] [Module ℝ α] : ContSet (ConZonotope α) α :=
  ⟨ConZonotope.construct⟩

instance {α : Type} [AddCommGroup α] [Module ℝ α] : ConvexSet (ConZonotope α) α :=
  ⟨ConZonotope.convex_construct⟩

/-- Compactness comes from `domain` being a bounded polytope, not from the
coefficient cube the constraints cut down. -/
instance {α : Type} [NormedAddCommGroup α] [NormedSpace ℝ α] : CompactSet (ConZonotope α) α :=
  ⟨ConZonotope.isCompact_construct⟩

instance {α : Type} [AddCommGroup α] [Module ℝ α] : OfPoint (ConZonotope α) α where
  ofPoint := ConZonotope.ofPoint
  mem_ofPoint := ConZonotope.mem_ofPoint

instance : Plus (ConZonotope (Vec ℝ n)) (Vec ℝ n) where
  plus := ConZonotope.plus
  plus_outer C₁ C₂ := (ConZonotope.plus_exact C₁ C₂).subset

instance : And (ConZonotope (Vec ℝ n)) (Vec ℝ n) where
  and := ConZonotope.and
  and_outer C₁ C₂ := (ConZonotope.and_exact C₁ C₂).subset

/-- A separate instance, so a caller that never combines does not depend on the
interpolation parameter this adds. -/
noncomputable instance : LinComb (ConZonotope (Vec ℝ n)) (Vec ℝ n) where
  linComb := ConZonotope.linComb
  linComb_outer := ConZonotope.linComb_outer

noncomputable instance : Reduce (ConZonotope (Vec ℝ n)) (Vec ℝ n) where
  reduce := ConZonotope.reduce
  reduce_outer := ConZonotope.reduce_outer

instance : Mtimes (Mat ℝ) (fun n => ConZonotope (Vec ℝ n)) where
  mtimes := ConZonotope.mtimes
  mtimes_outer M C := by
    simp only [ContSet.construct_mat, Scalar.toRealMat_real, Set.biUnion_singleton]
    exact (ConZonotope.mtimes_exact M C).subset

/-- The constrained-zonotope family over vectors. A generic theorem quantifies
over `S : ℕ → Type` and the elaborator cannot read that family off one member, so
a use site has to name it: `(S := 𝒞)`. -/
scoped notation "𝒞" => fun n => ConZonotope (Vec ℝ n)

/-- The same operation at an interval matrix, which a discretization wants and
no other class asks for. This is the last instance `LinearSys`
reachability needs, so a constrained zonotope now runs it. -/
noncomputable instance : Mtimes ℐ 𝒞 where
  mtimes := ConZonotope.mtimesIntervalMat
  mtimes_outer IM C := ConZonotope.mtimesIntervalMat_outer IM C

instance : Reindex 𝒞 where
  reindex e C := ConZonotope.map (reindexLin e) C
  reindex_exact e C := (ConZonotope.map_exact (reindexLin e) C).symm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
