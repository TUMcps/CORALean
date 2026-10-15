module

public import CORALean.ContDynamics.LinearSysDT.Operations.ObserveIntervalStepFloat
public import CORALean.ContSet.Zonotope.Float.Operations.Mtimes
public import CORALean.ContSet.Zonotope.Float.Operations.Plus

@[expose] public section

/-!
# The interval observer's state after `k` steps, in floats

[1, Alg. 1]: the state `observeIntervalStepFloat` reaches after `k` measurements, from the initial
set `R₀`: the nominal estimate starts at the center of `R₀`, the error at `R₀` itself, the
collected box at the origin and the disturbance set at `(-L) V ⊕ W`.

## References

* [1] M. Althoff. "Guaranteed State Estimation in CORA 2021". In Proc. of the 8th
      International Workshop on Applied Verification of Continuous and Hybrid Systems (ARCH21),
      EPiC Series in Computing, vol. 80, pp. 161-175, 2021.
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

def LinearSysDT.observeIntervalStateFloat (sys : LinearSysDT 𝕋 n) (L : Mat 𝕋 n sys.q)
    (R₀ W : Zonotope (Vec 𝕋 n)) (V : Zonotope (Vec 𝕋 sys.q)) (u : ℕ → Vec 𝕋 sys.m)
    (y : ℕ → Vec 𝕋 sys.q) : ℕ → LinearSysDT.ObserveIntervalStateFloat 𝕋 n
  | 0 => { x := Interval.point R₀.c, Rx := R₀, Rwv := Interval.point fun _ => zero,
           D := (Zonotope.mtimes (-L) V).plus W }
  | k + 1 =>
    sys.observeIntervalStepFloat L (u k) (y k) (sys.observeIntervalStateFloat L R₀ W V u y k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
