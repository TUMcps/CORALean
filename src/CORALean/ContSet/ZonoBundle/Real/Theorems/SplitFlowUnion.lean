module

public import CORALean.ContSet.ZonoBundle.Real.Theorems.SplitUnionEnclosingBox
public import CORALean.ContSet.ZonoBundle.Real.Operations.DirFlow
public import CORALean.ContSet.ZonoBundle.Real.Theorems.FlowIndexMax

@[expose] public section

/-!
# Splitting by the flow heuristic is exact

[1, Heuristic flow] puts the flow `f` into column `i` of the identity, whose determinant is `fᵢ`
(Cramer). With `i` the axis of largest `|fᵢ|` that is nonzero for any `f ≠ 0`, so the matrix is
invertible and the split exact. At `f = 0` it is not, and the paper has no flow to follow there.

## Inputs
* `f` – flow direction
* `zB` – zonotope bundle
* `i` – member index
* `j` – dimension to cut along

## Hypotheses
* `hf` – the flow is nonzero

## Conclusion
* the two halves together are exactly the bundle

## References

* [1] [M. Althoff and B. H. Krogh. "Zonotope Bundles for the Efficient Computation of Reachable
      Sets". 2011 50th IEEE Conference on Decision and Control and European Control Conference
      (CDC-ECC 2011), 2011.](../../../../../../references/2011/althoff-cdc-zonotope-bundles.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The flow heuristic's split is exact, for a nonzero flow. -/
theorem ZonoBundle.splitFlow_union (f : Vec ℝ n) (hf : f ≠ 0) (zB : ZonoBundle (Vec ℝ n))
    (i : Fin zB.k) (j : Fin n) : -- --- CONCL ---
    (zB.split (ZonoBundle.dirFlow f) (zB.enclosingBox (ZonoBundle.dirFlow f) i) j).fst.construct
      ∪ (zB.split (ZonoBundle.dirFlow f) (zB.enclosingBox (ZonoBundle.dirFlow f) i) j).snd.construct
      = zB.construct := by -- --- PROOF ---
  refine ZonoBundle.split_union_enclosingBox _ ?_ zB i j
  -- some coordinate of the flow is nonzero, so there is at least one axis
  obtain ⟨k, hk⟩ : ∃ k, f k ≠ 0 := by
    by_contra hc
    exact hf (funext fun k => not_not.mp fun h => hc ⟨k, h⟩)
  unfold ZonoBundle.dirFlow
  rcases hflow : ZonoBundle.flowIndex f with _ | a
  · exact absurd (List.argmax_eq_none.mp hflow) (List.ne_nil_of_mem (List.mem_finRange k))
  · -- the determinant of `I` with column `a` replaced by `f` is `f a`
    have hdet : ((1 : Mat ℝ n n).updateCol a f).det = f a := by
      rw [← Matrix.cramer_apply, Matrix.cramer_one]; rfl
    have hfa : f a ≠ 0 := fun h0 =>
      hk (abs_nonpos_iff.mp ((ZonoBundle.flowIndex_max k _ hflow).trans (by rw [h0, abs_zero])))
    simp only [hdet]
    exact isUnit_iff_ne_zero.mpr hfa

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
