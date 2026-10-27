module

public import CORALean.ContDynamics.NonlinearSys.NonlinearSys

@[expose] public section

/-!
# `linPoint`, the point a step linearizes at

Line 3 of [1, Alg. 1], which its eq. (6) spells out: the state expansion point is the center of
the set the step starts from, carried half a step along the field, and the input expansion point
is the center of the input set — [2, Sec. V]'s `z✱ = ĉ + (r/2) f(ĉ, mid(p))`. Half a step, so
the point sits where the flow is in the middle of the step; that makes `A` and `Ψ` of eq. (32)
functions of the step size, which [1, Def. 5] compares. `Recenter.center` is what a
representation offers as its center. There is no `y✱`: this is the ODE specialization of `Alg. 1`.

## Inputs
* `sys` – system
* `Δt` – step size
* `R` – start set
* `U` – input set

## Output
* the state and input expansion points

## References

* [1] [M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive Reachability Algorithms
      for Nonlinear Systems Using Abstraction Error Analysis". Nonlinear Analysis: Hybrid Systems,
      2022.](../../../../../references/2022/wetzlinger-nahs-abstraction-error.md)
* [2] [M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Nonlinear Systems with
      Uncertain Parameters using Conservative Linearization". 2008 47th IEEE Conference on Decision
      and Control, 2008.](../../../../../references/2008/althoff-cdc-conservative-linearization.md)
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Recenter (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `z✱(t_k)`: the center of `R(t_k)` advanced by half a step along `f`, paired
with the center of the input set. -/
noncomputable def NonlinearSys.linPoint (sys : NonlinearSys n m) (Δt : ℝ) (R : S n) (U : S m) :
    Vec ℝ n × Vec ℝ m :=
  let us := Recenter.center U                          -- 6. u✱ = center(U)
  let c := Recenter.center R                           -- 6. center(R(t_k))
  (c + (Δt / 2) • sys.f c us, us)                      -- 6. x✱ = center + ½Δt f(center)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
