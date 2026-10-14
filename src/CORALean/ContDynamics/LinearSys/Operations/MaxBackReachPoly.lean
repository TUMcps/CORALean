module

public import CORALean.ContSet.Capsule.Real.Operations.SupportBound
public import CORALean.ContSet.HPolytope.Real.Operations.Comap
public import CORALean.ContSet.HPolytope.Real.Operations.MinkDiffOf
public import CORALean.ContSet.Zonotope.Real.Operations.SupportBound

@[expose] public section

/-!
# `Alg. 3` lines 4-5: the eroded polytope

`maxBackReachPoly`: [1, Alg. 3] lines 4-5, `X ⊖ F box(X_end) ⊖ B_μ`, one of the two polytopes
of the inner approximated homogeneous time-interval solution (21).

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of Perturbed
      Continuous-Time Linear Systems Using Set Propagation". IEEE Transactions on
      Automatic Control, 71(1):352-367, 2026.
-/

-- Authors:       Claude Sonnet 5
-- Written:       19-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lines 4-5: `X ⊖ F box(X_end) ⊖ B_μ`, one of the two polytopes of the inner
approximated homogeneous time-interval solution (21). -/
noncomputable def LinearSys.maxBackReachPoly (X : HPolytope (Vec ℝ n))
    (FB : Zonotope (Vec ℝ n)) (μ : ℝ) : HPolytope (Vec ℝ n) :=
  let XF := X.minkDiffOf FB.construct fun i => FB.supportBound (X.A i)  -- ⊖ F box(X_end)
  XF.minkDiffOf (⟨0, 0, μ⟩ : Capsule n).construct                       -- ⊖ B_μ
    fun i => (⟨0, 0, μ⟩ : Capsule n).supportBound (XF.A i)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
