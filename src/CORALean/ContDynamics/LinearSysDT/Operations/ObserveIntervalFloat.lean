module

public import CORALean.ContDynamics.LinearSysDT.Definitions.ObserveIntervalStateFloat
public import CORALean.ContDynamics.LinearSysDT.Operations.ErrMatFloat
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Operations.MtimesIntervalMat
public import CORALean.ContSet.Interval.Float.Operations.Point
public import CORALean.ContSet.Zonotope.Float.Operations.Mtimes
public import CORALean.ContSet.Zonotope.Float.Operations.MtimesIntervalMat
public import CORALean.ContSet.Zonotope.Float.Operations.Plus

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
open CORALean.Float FloatOps


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

def LinearSysDT.aux_observeIntervalStepFloat (sys : LinearSysDT 𝕋 n) (L : Mat 𝕋 n sys.q)
    (u : Vec 𝕋 sys.m) (y : Vec 𝕋 sys.q) (s : LinearSysDT.ObserveIntervalStateFloat 𝕋 n) :
    LinearSysDT.ObserveIntervalStateFloat 𝕋 n :=
  let IM := LinearSysDT.errMatFloat sys.A L sys.C                     -- `A - L C`, rounded
  { x := ((Interval.mtimesIntervalMat IM s.x).plus
      (Interval.mtimes sys.B (Interval.point u))).plus
      (Interval.mtimes L (Interval.point y))                          -- observer update
    Rx := Zonotope.mtimesIntervalMat IM s.Rx                          -- the error through `A - L C`
    Rwv := s.Rwv.plus s.D.interval                                    -- add the box of `D`
    D := Zonotope.mtimesIntervalMat IM s.D }                          -- `D` through `A - L C`

def LinearSysDT.aux_observeIntervalStateFloat (sys : LinearSysDT 𝕋 n) (L : Mat 𝕋 n sys.q)
    (R₀ W : Zonotope (Vec 𝕋 n)) (V : Zonotope (Vec 𝕋 sys.q)) (u : ℕ → Vec 𝕋 sys.m)
    (y : ℕ → Vec 𝕋 sys.q) : ℕ → LinearSysDT.ObserveIntervalStateFloat 𝕋 n
  | 0 => { x := Interval.point R₀.c, Rx := R₀, Rwv := Interval.point fun _ => zero,
           D := (Zonotope.mtimes (-L) V).plus W }
  | k + 1 =>
    sys.aux_observeIntervalStepFloat L (u k) (y k)
      (sys.aux_observeIntervalStateFloat L R₀ W V u y k)


-- =====================================  MAIN DEFINITION  ====================================== --

def LinearSysDT.observeIntervalFloat (sys : LinearSysDT 𝕋 n) (L : Mat 𝕋 n sys.q)
    (R₀ W : Zonotope (Vec 𝕋 n)) (V : Zonotope (Vec 𝕋 sys.q)) (u : ℕ → Vec 𝕋 sys.m)
    (y : ℕ → Vec 𝕋 sys.q) (k : ℕ) :
    Interval (Vec 𝕋 n) :=
  let s := sys.aux_observeIntervalStateFloat L R₀ W V u y k
  let E := s.Rx.interval.plus s.Rwv                                  -- `box(R_x) + R_wv`
  s.x.plus E                                                         -- `x̂ + E`

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
