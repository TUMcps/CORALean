module

public import CORALean.ContDynamics.LinearSysDT.LinearSysDT
public import CORALean.ContSet.Zonotope.Real.Operations.Mtimes
public import CORALean.ContSet.Zonotope.Real.Operations.Plus
public import CORALean.ContSet.Zonotope.Real.Operations.OfPoint
public import CORALean.ContSet.Zonotope.Real.Operations.Reduce

@[expose] public section

/-!
# The set-propagation observer

[1, Eq. 6], the set-based Luenberger observer `S_{k+1} = (A - L C) S_k ⊕ B u_k ⊕ L y_k ⊕ (-L) V ⊕
W`, as CORA runs it for `FRad-C` (`priv_observe_intersectionFreeAdaptive`, the gain from the
current set's generators), `PRad-E` and `Nom-G` (`priv_observe_intersectionFree`, a fixed gain),
each step reduced to `order`; the gain is a function of the current set, which covers both. No
strip widths enter. As in CORA, neither `c` nor `E`, `D`, `k`, `F` enters (the counterexamples
`observePropagation_state_offset_counterexample` and its siblings). [2, Sec. 5]: at the gain
`Zonotope.luenbergerGain`, the sets of Combastel's zonotopic Kalman filter (Eqs. 29-30), reduced
after the step where [2] applies `↓_{q,W}` before it; its covariation `P` is not computed.

## Inputs
* `sys` – system
* `gain` – gain function
* `order` – zonotope order
* `W` – disturbance zonotope
* `R₀` – initial zonotope
* `V` – noise zonotope
* `u` – inputs
* `y` – measurements

## Output
* the observer's state set after each number of steps

## References

* [1] M. Althoff. "Guaranteed State Estimation in CORA 2021". In Proc. of the 8th
      International Workshop on Applied Verification of Continuous and Hybrid Systems (ARCH21),
      EPiC Series in Computing, vol. 80, pp. 161-175, 2021.
* [2] C. Combastel. "Zonotopes and Kalman observers: Gain optimality under distinct uncertainty
      paradigms and robust convergence". Automatica, 55:265-273, 2015.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix CORALean.Real

variable {n p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `S k`, the set the observer holds for the state at step `k`. -/
noncomputable def LinearSysDT.observePropagation (sys : LinearSysDT ℝ n)
    (gain : Zonotope (Vec ℝ n) → Mat ℝ n sys.q) (order : ℕ) (W R₀ : Zonotope (Vec ℝ n))
    (V : Zonotope (Vec ℝ sys.q)) (u : ℕ → Vec ℝ sys.m)
    (y : ℕ → Vec ℝ sys.q) : ℕ → Zonotope (Vec ℝ n)
  | 0 => R₀
  | k + 1 =>
    let S := sys.observePropagation gain order W R₀ V u y k
    let L := gain S  -- the observer gain at this step
    let S' := ((((Zonotope.mtimes (sys.A - L * sys.C) S).plus
      (Zonotope.ofPoint (sys.B *ᵥ u k))).plus
      (Zonotope.ofPoint (L *ᵥ y k))).plus (Zonotope.mtimes (-L) V)).plus W  -- (6)
    S'.reduce order

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
