module

public import CORALean.ContDynamics.NonlinearSys.NonlinearSys

@[expose] public section

/-!
# `linPoint`, the point a step linearizes at

Line 3 of [1, Alg. 1], which its eq. (6) spells out: the state expansion point
is the centre of the set the step starts from, carried half a step along the
field, and the input expansion point is the centre of the input set — [2, Sec. V]'s
`z✱ = ĉ + (r/2) f(ĉ, mid(p))`, read as moving the state block of `ĉ` alone.

Half a step and not none: the linearization is meant to be good over the whole
of `[t_k, t_{k+1}]`, so the point is put where the flow is in the middle of it.
That is also what makes `A` and `Ψ` of eq. (32) functions of the step size,
which is what [1, Def. 5] compares two of.

`Recentre.centre` is what a representation offers as its centre; nothing here
asks it to be a barycentre, and a representation without one cannot run this
line. `xs` and `us` spell `x✱` and `u✱`, which are no Lean identifiers, and are
`LinStep`'s names for them. No algebraic equation and so no `y✱`: this is the
ordinary-differential specialization [1] gives directly under its `Alg. 1`.

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive
      Reachability Algorithms for Nonlinear Systems Using Abstraction Error
      Analysis". Nonlinear Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
* [2] M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Nonlinear
      Systems with Uncertain Parameters using Conservative Linearization". In
      Proc. of the 47th IEEE Conference on Decision and Control (CDC), 2008,
      pp. 4042-4048.
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Recentre (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `z✱(t_k)`: the centre of `R(t_k)` advanced by half a step along `f`, paired
with the centre of the input set. -/
noncomputable def NonlinearSys.linPoint (sys : NonlinearSys n m) (Δt : ℝ) (R : S n) (U : S m) :
    Vec ℝ n × Vec ℝ m :=
  let us := Recentre.centre U                          -- 6. u✱ = center(U)
  let c := Recentre.centre R                           -- 6. center(R(t_k))
  (c + (Δt / 2) • sys.f c us, us)                      -- 6. x✱ = center + ½Δt f(center)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
