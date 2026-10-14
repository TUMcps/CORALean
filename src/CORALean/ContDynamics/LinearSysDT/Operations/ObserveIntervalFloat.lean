module

public import CORALean.ContDynamics.LinearSysDT.Operations.ObserveIntervalStateFloat
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# The interval observer, in floats

CORA's `observe_interval` (`Hinf-G`), [1, Alg. 1]: the state after `k` measurements is the
nominal box plus the box of the error, `x̂ + (box(R_x) + R_wv)`, all in directed rounding with the
gain `L` fixed. Soundness is `observeIntervalFloat_outer`.

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

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def LinearSysDT.observeIntervalFloat (sys : LinearSysDT 𝕋 n) (L : Mat 𝕋 n sys.q)
    (R₀ W : Zonotope (Vec 𝕋 n)) (V : Zonotope (Vec 𝕋 sys.q)) (u : ℕ → Vec 𝕋 sys.m)
    (y : ℕ → Vec 𝕋 sys.q) (k : ℕ) :
    Interval (Vec 𝕋 n) :=
  let s := sys.observeIntervalStateFloat L R₀ W V u y k
  let E := s.Rx.interval.plus s.Rwv                                  -- `box(R_x) + R_wv`
  s.x.plus E                                                         -- `x̂ + E`

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
