module

public import CORALean.ContSet.ContSet.ContSet
public import Mathlib.Analysis.Convex.Hull

@[expose] public section

/-!
# A convex subtrahend only has to be subtracted at the points that span it

[1, Lemma 1]: the difference against a convex subtrahend is already the intersection of the
differences against finitely many of its points. A point that survives every `v ∈ V` survives all of
`convexHull ℝ V`, because `{z | x + z ∈ S}` is a translate of the convex `S`. Stated at any spanning
`V` rather than the vertices the paper names: the proof uses `T ⊆ convexHull ℝ V`, and the vertex
set of a compact convex `T` is one such `V`, finite for a zonotope. Convexity is asked of the
*minuend*, not — as printed — of the subtrahend: that is where the hull argument runs.

## Inputs
* `S` – minuend
* `T` – subtrahend
* `V` – spanning set

## Hypotheses
* `hS` – `S` convex
* `hVT` – `V ⊆ T`
* `hT` – `T` in the convex hull of `V`

## Conclusion
* `S ⊖ T` is the intersection of the differences `S ⊖ {v}` over `V`

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes".
      arXiv, 2015.
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Lemma 1]: against a minuend that is convex, subtracting a spanning set
`V` point by point already gives the whole difference. -/
theorem minkowskiDiff_eq_iInter (S T V : Set α) (hS : Convex ℝ S) (hVT : V ⊆ T)
    (hT : T ⊆ convexHull ℝ V) :
    minkowskiDiff S T = ⋂ v ∈ V, minkowskiDiff S {v} := by -- --- PROOF ---
  ext x
  simp only [Set.mem_iInter, minkowskiDiff, Set.mem_setOf_eq, Set.mem_singleton_iff,
    forall_eq]
  refine ⟨fun hx v hv => hx v (hVT hv), fun hx y hy => ?_⟩
  -- the points `z` that `x` may still absorb form a translate of `S`, so convex
  exact convexHull_min (fun v hv => hx v hv) (hS.translate_preimage_right x) (hT hy)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
