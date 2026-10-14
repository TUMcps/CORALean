module

public import CORALean.ContDynamics.LinearSysDT.Definitions.ObserveIntervalStateFloat
public import CORALean.ContDynamics.LinearSysDT.Operations.ErrMatFloat
public import CORALean.ContSet.Zonotope.Float.Operations.MtimesIntervalMat
public import CORALean.ContSet.Interval.Float.Operations.MtimesIntervalMat
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Operations.Point
public import CORALean.ContSet.Conversion.Float.Zonotope_to_Interval

@[expose] public section

/-!
# One step of the interval observer, in floats

[1, Alg. 1], one step in directed rounding: the nominal estimate `A x̂ + u + L (y - C x̂)` is
`(A - L C) x̂ + u + L y`, with `A - L C` the interval matrix `errMatFloat`, the initial error and
the disturbance set go through the same interval matrix, and the box of the disturbance set is
added to the collected box.

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

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def LinearSysDT.observeIntervalStepFloat (sys : LinearSysDT 𝕋 n) (C : Mat 𝕋 p n)
    (L : Mat 𝕋 n p) (u : Vec 𝕋 n) (y : Vec 𝕋 p) (s : LinearSysDT.ObserveIntervalStateFloat 𝕋 n) :
    LinearSysDT.ObserveIntervalStateFloat 𝕋 n :=
  let IM := LinearSysDT.errMatFloat sys.A L C                         -- `A - L C`, rounded
  { x := ((Interval.mtimesIntervalMat IM s.x).plus (Interval.point u)).plus
      (Interval.mtimes L (Interval.point y))                          -- observer update
    Rx := Zonotope.mtimesIntervalMat IM s.Rx                          -- the error through `A - L C`
    Rwv := s.Rwv.plus s.D.interval                                    -- add the box of `D`
    D := Zonotope.mtimesIntervalMat IM s.D }                          -- `D` through `A - L C`

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
