module

public import CORALean.ContDynamics.LinearSysDT.Operations.ErrMatFloat
public import CORALean.ContSet.Zonotope.Float.Operations.MtimesIntervalMat
public import CORALean.ContSet.Zonotope.Float.Operations.Mtimes
public import CORALean.ContSet.Zonotope.Float.Operations.Plus
public import CORALean.ContSet.Zonotope.Float.Operations.Point
public import CORALean.ContSet.Zonotope.Float.Operations.Reduce

@[expose] public section

/-!
# The set-propagation observer, in floats

CORA's `observe_propagation`, [1, Eq. 6], in directed rounding: `S' = (A - L C) S ⊕ B u ⊕ L y ⊕
(-L) V ⊕ W`, reduced to `order`, with the gain `L` a function of the zonotope it is applied to.
`A - L C` is the interval matrix `errMatFloat`, `L y` the product of `L` with the point `y`.
Soundness is `observePropagationFloat_outer`.

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
* the observer's float state set after each number of steps

## References

* [1] M. Althoff. "Guaranteed State Estimation in CORA 2021". 8th International Workshop on Applied
      Verification of Continuous and Hybrid Systems (ARCH21), 2021.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `S k`, the set the observer holds for the state at step `k`. -/
def LinearSysDT.observePropagationFloat (sys : LinearSysDT 𝕋 n)
    (gain : Zonotope (Vec 𝕋 n) → Mat 𝕋 n sys.q) (order : ℕ) (W R₀ : Zonotope (Vec 𝕋 n))
    (V : Zonotope (Vec 𝕋 sys.q)) (u : ℕ → Vec 𝕋 sys.m)
    (y : ℕ → Vec 𝕋 sys.q) : ℕ → Zonotope (Vec 𝕋 n)
  | 0 => R₀
  | k + 1 =>
    let S := sys.observePropagationFloat gain order W R₀ V u y k
    let L := gain S                                                  -- the gain at this step
    let S' := (((((Zonotope.mtimesIntervalMat (LinearSysDT.errMatFloat sys.A L sys.C) S).plus
      (Zonotope.mtimes sys.B (Zonotope.point (u k)))).plus
      (Zonotope.mtimes L (Zonotope.point (y k)))).plus
      (Zonotope.mtimes (-L) V)).plus W)          -- (6)
    S'.reduce order

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
