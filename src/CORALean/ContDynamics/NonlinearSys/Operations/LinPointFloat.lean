module

public import CORALean.ContDynamics.NonlinearSys.Definitions.FloatModel
public import CORALean.ContSet.Conversion.Float.Interval_to_Zonotope
public import CORALean.ContSet.Interval.Float.Operations.Point

@[expose] public section

/-!
# `linPointFloat`, the point a float step linearizes at

`linPoint` in `𝕋`: line 3 of [1, Alg. 1], spelled out by its eq. (6) — the
centre of the set the step starts from carried half a step along the field, and
the centre of the input set. The field at the centre is not a float: it is the
midpoint of the model's enclosure there, any point of which would do.

Nothing is rounded in a direction that matters. The point only has to be *some*
point, since no guarantee depends on where a step linearizes; the run pays for a
poor one in a larger remainder, never in soundness.

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive
      Reachability Algorithms for Nonlinear Systems Using Abstraction Error
      Analysis". Nonlinear Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `z✱(t_k)` in floats: the stored centre of `R` advanced by `½Δt` times the
model's field there, paired with the stored centre of `U`. -/
def NonlinearSys.FloatModel.linPointFloat (fm : NonlinearSys.FloatModel 𝕋 n m) (Δt : 𝕋)
    (R : Zonotope (Vec 𝕋 n)) (U : Zonotope (Vec 𝕋 m)) : Vec 𝕋 n × Vec 𝕋 m :=
  let us := U.c                                                     -- 6. u✱ = center(U)
  let c := R.c                                                      -- 6. center(R(t_k))
  let fc := (fm.f (Interval.point c) (Interval.point us)).center    -- f(center, u✱)
  (fun i => addUp (c i) (mulUp (half Δt) (fc i)), us)               -- 6. x✱ = center + ½Δt f

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
