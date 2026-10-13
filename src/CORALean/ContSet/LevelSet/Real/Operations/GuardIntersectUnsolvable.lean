import CORALean.ContSet.LevelSet.Real.Operations.IntersectLevelSetBox

/-!
# Guard intersection for a constraint not solvable for any variable

[1, Prop. 2]'s model: the box `I` cut by `x(k) = p_k(x)` (`intersect`), with
`[D_l, D_u]` in the `k`-th coordinate of the box remainder. `p_k` is the part of eq. (11)
free of `x(k)` and `[D_l, D_u]` eq. (12)'s interval; how they arise from a Taylor series of the
guard function is what `Theorems.GuardIntersectUnsolvableSubset` takes as hypotheses — with
eq. (11)'s sign of `v(x)` corrected, as that file says.

## References

* [1] N. Kochdumper and M. Althoff. "Reachability Analysis for Hybrid Systems with Nonlinear
      Guard Sets". In Proc. of the 23rd ACM International Conference on Hybrid Systems:
      Computation and Control (HSCC), 2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def guardIntersectUnsolvable (I : Interval (Vec ℝ n)) (k : Fin n) (pk : Vec ℝ n → ℝ)
    (Dl Du : ℝ) : TaylorModelOn n :=
  let h := (intersectLevelSetBox I k pk).p
  let B : Interval (Vec ℝ n) := ⟨Pi.single k Dl, Pi.single k Du⟩
  ⟨h, B, I⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
