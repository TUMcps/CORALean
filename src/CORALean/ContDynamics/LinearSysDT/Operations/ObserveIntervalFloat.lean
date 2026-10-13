import CORALean.ContDynamics.LinearSysDT.Operations.ObserveIntervalStateFloat

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

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def LinearSysDT.observeIntervalFloat (sys : LinearSysDT 𝕋 n) (C : Mat 𝕋 p n) (L : Mat 𝕋 n p)
    (R₀ W : Zonotope (Vec 𝕋 n)) (V : Zonotope (Vec 𝕋 p)) (u : ℕ → Vec 𝕋 n)
    (y : ℕ → Vec 𝕋 p) (k : ℕ) :
    Interval (Vec 𝕋 n) :=
  let s := sys.observeIntervalStateFloat C L R₀ W V u y k
  let E := s.Rx.interval.plus s.Rwv                                  -- `box(R_x) + R_wv`
  s.x.plus E                                                         -- `x̂ + E`

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
