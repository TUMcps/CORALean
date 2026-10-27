module

public import CORALean.ContSet.Zonotope.Float.Theorems.ConvexHullSubsetLinComb
public import CORALean.ContSet.Zonotope.Float.Theorems.PlusOuter
public import CORALean.ContSet.Zonotope.Real.Theorems.CenterMemConstruct
public import CORALean.Specification.STL.Operations.DepReachIntervalFloat

@[expose] public section

/-!
# The time interval reachable set over floats encloses the exact one

The exact set `conv(H(t_i), H(t_{i+1})) ⊕ P(t_{i+1}) ⊕ C_i` of line 9 of [1, Alg. 1] lies inside the
float `R(τ_i)`: the convex hull of two float zonotopes lies in their `linComb`
(`convexHull_subset_linComb`) and the sums are `plus_outer`. The real `STL.depReachInterval` holds
the same exact set, but its `linComb` depends on the generators of the real states, which the float
states do not keep, so the exact set is the common bound.
## Inputs
* `sF` – float state at the step start
* `sF'` – float state at the step end
* `sR` – real state at the step start
* `sR'` – real state at the step end
* `E` – exact set standing for `C_i`
* `E'` – exact set standing for `C_{i+1}`

## Hypotheses
* `h` – the float state at the step start encloses the real one
* `h'` – the float state at the step end encloses the real one

## Conclusion
* the exact reachable set over the interval lies inside the float one
## References

* [1] [N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, 2024.](../../../../../references/2024/kochdumper-nahs-stl-lti-verification.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Pointwise Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The float `R(τ_i)` holds the exact `conv(H(t_i), H(t_{i+1})) ⊕ P(t_{i+1}) ⊕ C_i`. -/
theorem STL.depReachIntervalFloat_outer {sF sF' : STL.DepReachStateFloat 𝕋 n}
    {sR sR' : STL.DepReachState n} {E E' : Set (Vec ℝ n)} (h : sF.Encloses sR E)
    (h' : sF'.Encloses sR' E') : -- --- CONCL ---
    (convexHull ℝ (sR.H.construct ∪ sR'.H.construct) + (sR'.Pc.construct + sR'.D.construct)) +
      E ⊆ (STL.depReachIntervalFloat sF sF').construct := by -- --- PROOF ---
  -- both real hulls lie inside the float zonotopes, which are nonempty as they hold the centers
  have n₁ : sF.H.construct.Nonempty :=
    ⟨_, h.1 (Real.Zonotope.center_mem_construct sR.H)⟩
  have n₂ : sF'.H.construct.Nonempty :=
    ⟨_, h'.1 (Real.Zonotope.center_mem_construct sR'.H)⟩
  unfold STL.depReachIntervalFloat
  refine (Set.add_subset_add ?_ h.2.2.2).trans (Float.Zonotope.plus_outer _ _)
  refine (Set.add_subset_add ?_ ?_).trans (Float.Zonotope.plus_outer _ _)
  · exact (convexHull_mono (Set.union_subset_union h.1 h'.1)).trans
      (Float.Zonotope.convexHull_subset_linComb _ _ n₁ n₂)
  · exact (Set.add_subset_add h'.2.1 h'.2.2.1).trans (Float.Zonotope.plus_outer _ _)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
