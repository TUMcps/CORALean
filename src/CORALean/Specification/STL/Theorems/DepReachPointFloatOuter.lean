module

public import CORALean.ContSet.Zonotope.Float.Theorems.PlusOuter
public import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact
public import CORALean.Specification.STL.Operations.DepReachPointFloat

@[expose] public section

/-!
# The time point reachable set over floats encloses the real one

The real `R(t_i)` of [1, Alg. 1] is the Minkowski sum of its three zonotopes
(`Zonotope.plus_exact`), each of which the float state holds, and the float sum holds the sum of the
float zonotopes (`plus_outer`).
## Inputs
* `sF` – float state
* `sR` – real state
* `E` – exact set standing for `C_i`

## Hypotheses
* `h` – the float state encloses the real one

## Conclusion
* the real reachable set at the time point lies inside the float one
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

/-- The float `R(t_i)` holds the real `R(t_i)` of a state it encloses. -/
theorem STL.depReachPointFloat_outer {sF : STL.DepReachStateFloat 𝕋 n} {sR : STL.DepReachState n}
    {E : Set (Vec ℝ n)} (h : sF.Encloses sR E) : -- --- CONCL ---
    (STL.depReachPoint sR).construct ⊆ (STL.depReachPointFloat sF).construct := by -- --- PROOF ---
  unfold STL.depReachPoint STL.depReachPointFloat
  rw [← Real.Zonotope.plus_exact, ← Real.Zonotope.plus_exact]
  exact (Set.add_subset_add h.1 (Set.add_subset_add h.2.1 h.2.2.1)).trans
    ((Set.add_subset_add (Set.Subset.refl _) (Float.Zonotope.plus_outer _ _)).trans
      (Float.Zonotope.plus_outer _ _))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
