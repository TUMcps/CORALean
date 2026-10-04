import CORALean.ContDynamics.LinearSysDT.Operations.ObserveIntervalStepFloat
import CORALean.ContSet.Zonotope.Float.Operations.Mtimes
import CORALean.ContSet.Zonotope.Float.Operations.Plus

/-!
# The interval observer's state after `k` steps, in floats

[1, Alg. 1]: the state `observeIntervalStepFloat` reaches after `k` measurements, from the initial
set `R₀`: the nominal estimate starts at the centre of `R₀`, the error at `R₀` itself, the
collected box at the origin and the disturbance set at `(-L) V ⊕ W`.

## References

* [1] M. Althoff. "Guaranteed State Estimation in CORA 2021". In Proc. of the 8th
      International Workshop on Applied Verification of Continuous and Hybrid Systems (ARCH21),
      EPiC Series in Computing, vol. 80, pp. 161-175, 2021.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def LinearSysDT.observeIntervalStateFloat (sys : LinearSysDT 𝕋 n) (C : Mat 𝕋 p n)
    (L : Mat 𝕋 n p) (R₀ W : Zonotope 𝕋 n) (V : Zonotope 𝕋 p) (u : ℕ → Vec 𝕋 n)
    (y : ℕ → Vec 𝕋 p) : ℕ → LinearSysDT.ObserveIntervalStateFloat 𝕋 n
  | 0 => { x := Interval.point R₀.c, Rx := R₀, Rwv := Interval.point fun _ => zero,
           D := (Zonotope.mtimes (fun i j => neg (L i j)) V).plus W }
  | k + 1 =>
    sys.observeIntervalStepFloat C L (u k) (y k) (sys.observeIntervalStateFloat C L R₀ W V u y k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
