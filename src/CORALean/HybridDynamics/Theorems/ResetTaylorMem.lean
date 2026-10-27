module

public import CORALean.HybridDynamics.Definitions.ResetTaylor
public import CORALean.ContSet.LevelSet.Real.Definitions.TaylorSeries
public import CORALean.Global.TaylorLagrangeConvex

@[expose] public section

/-!
# The reset's Taylor expansion encloses it, coordinate by coordinate

[1, Eq. 14] corrected: each coordinate `r₍ⱼ₎(x) - p₍ⱼ₎(x)` is its own Lagrange remainder, at
its own `ξⱼ`, so `r(x) - p(x)` lies in the product of the coordinate sets
`Lⱼ = {((x - c)ᵀ∇)^{γ+1} r₍ⱼ₎(ξ) / (γ+1)! | ξ, x ∈ C}` (`lagrangeSet`), not in [1]'s set with
one `ξ` shared by all coordinates. And `ξ` lies on the segment from `c` to `x`, so the set
it ranges over has to contain that segment: `C` is convex and contains `F`, `c` and `x`. A
polynomial zonotope `F` need not be convex; [1]'s own evaluation encloses `F` by a box before
bounding the remainder by interval arithmetic, which is this statement at `C` the box.

## Inputs
* `r` – reset
* `γ` – Taylor order
* `C` – convex set
* `c` – expansion point
* `x` – state
* `j` – coordinate

## Hypotheses
* `hr` – reset coordinates smooth enough
* `hC` – the set is convex
* `hc` – expansion point lies in the set
* `hx` – state lies in the set

## Conclusion
* the coordinate remainder lies in its Lagrange set

## References

* [1] [N. Kochdumper and M. Althoff. "Reachability Analysis for Hybrid Systems with Nonlinear Guard
      Sets". Proceedings of the 23rd International Conference on Hybrid Systems: Computation and
      Control, 2020.](../../../../references/2020/kochdumper-hscc-nonlinear-guards.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


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
