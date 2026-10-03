import CORALean.HybridDynamics.Definitions.ResetTaylor
import CORALean.ContSet.LevelSet.Real.Definitions.TaylorSeries
import CORALean.Global.TaylorLagrangeConvex

/-!
# The reset's Taylor expansion encloses it, coordinate by coordinate

[1, Eq. 14] corrected: each coordinate `r₍ⱼ₎(x) - p₍ⱼ₎(x)` is its own Lagrange remainder, at
its own `ξⱼ`, so `r(x) - p(x)` lies in the product of the coordinate sets
`Lⱼ = {((x - c)ᵀ∇)^{γ+1} r₍ⱼ₎(ξ) / (γ+1)! | ξ, x ∈ C}` (`lagrangeSet`), not in [1]'s set with
one `ξ` shared by all coordinates. And `ξ` lies on the segment from `c` to `x`, so the set
it ranges over has to contain that segment: `C` is convex and contains `F`, `c` and `x`. A
polynomial zonotope `F` need not be convex; [1]'s own evaluation encloses `F` by a box before
bounding the remainder by interval arithmetic, which is this statement at `C` the box.

## References

* [1] N. Kochdumper and M. Althoff. "Reachability Analysis for Hybrid Systems with Nonlinear
      Guard Sets". In Proc. of the 23rd ACM International Conference on Hybrid Systems:
      Computation and Control (HSCC), 2020.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem resetTaylor_mem {r : Vec ℝ n → Vec ℝ n} {γ : ℕ}
    (hr : ∀ j, ContDiff ℝ (γ + 1) (fun y => r y j)) {C : Set (Vec ℝ n)} (hC : Convex ℝ C)
    {c x : Vec ℝ n} (hc : c ∈ C) (hx : x ∈ C) (j : Fin n) :
    r x j - resetTaylorPoly r γ c x j ∈ lagrangeSet (fun y => r y j) γ c C := by
  obtain ⟨ξ, hξ, h⟩ := taylor_lagrange_convex (hr j) hC hc hx
  refine ⟨ξ, hξ, x, hx, ?_⟩
  simp only [resetTaylorPoly]
  linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
