import CORALean.ContDynamics.LinearSysDT.LinearSysDT
import CORALean.ContSet.Zonotope.Real.Operations.Mtimes
import CORALean.ContSet.Zonotope.Real.Operations.Plus
import CORALean.ContSet.Zonotope.Real.Operations.OfPoint
import CORALean.ContSet.Zonotope.Real.Operations.Reduce

/-!
# The set-propagation observer

[1, Eq. 6], the set-based Luenberger observer
`S_{k+1} = (A - L C) S_k ⊕ B u_k ⊕ L y_k ⊕ (-L) V ⊕ W`,
as CORA runs it for `FRad-C` (`priv_observe_intersectionFreeAdaptive`, the gain computed from
the current set's generators), `PRad-E` and `Nom-G` (`priv_observe_intersectionFree`, a gain
fixed offline): each step then reduced to `order`. The gain is a function of the current set,
which covers both. No intersection is taken, so no strip widths enter; the input `u` is in state
coordinates (`B u` folded, as `LinearSysDT` folds it).

## References

* [1] M. Althoff. "Guaranteed State Estimation in CORA 2021". In Proc. of the 8th
      International Workshop on Applied Verification of Continuous and Hybrid Systems (ARCH21),
      EPiC Series in Computing, vol. 80, pp. 161-175, 2021.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix CORALean.Real

variable {n p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `S k`, the set the observer holds for the state at step `k`. -/
noncomputable def LinearSysDT.observePropagation (sys : LinearSysDT ℝ n) (C : Mat ℝ p n)
    (gain : Zonotope (Vec ℝ n) → Mat ℝ n p) (order : ℕ) (W R₀ : Zonotope (Vec ℝ n))
    (V : Zonotope (Vec ℝ p)) (u : ℕ → Vec ℝ n) (y : ℕ → Vec ℝ p) : ℕ → Zonotope (Vec ℝ n)
  | 0 => R₀
  | k + 1 =>
    let S := sys.observePropagation C gain order W R₀ V u y k
    let L := gain S  -- the observer gain at this step
    let S' := ((((Zonotope.mtimes (sys.A - L * C) S).plus (Zonotope.ofPoint (u k))).plus
      (Zonotope.ofPoint (L *ᵥ y k))).plus (Zonotope.mtimes (-L) V)).plus W  -- (6)
    S'.reduce order

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
