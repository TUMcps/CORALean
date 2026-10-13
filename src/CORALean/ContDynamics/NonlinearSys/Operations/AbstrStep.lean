module

public import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalStep
public import CORALean.ContDynamics.LinearSys.Operations.TimePointStep
public import CORALean.ContDynamics.NonlinearSys.Operations.AbstrErrLoop
public import CORALean.ContDynamics.NonlinearSys.Operations.AbstrInit
public import CORALean.ContDynamics.NonlinearSys.Operations.LinInput
public import CORALean.ContDynamics.NonlinearSys.Operations.LinPoint
public import CORALean.ContDynamics.NonlinearSys.Operations.Linearize

@[expose] public section

/-!
# `Alg. 1` lines 3-16: one iteration of the main loop

[1, Alg. 1]'s step. Lines 4-5 are the caller's: `taylor` differentiates `f`
and nothing in this tree does, so `lin` hands back the `A` and `B` a
linearization at the point line 3 computed would give, exactly as `LinStep`
carries them. That is also why the certificate sits on the theorems and not
here.

One departure, forced: lines 8-11 may give out, so a step is an `Option`.

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive
      Reachability Algorithms for Nonlinear Systems Using Abstraction Error
      Analysis". Nonlinear Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
-/

-- Authors:       Claude Sonnet 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable [∀ n, OfPoint (S n) (Vec ℝ n)] [∀ n, Recentre (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S] [Real.OfInterval S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lines 3-16: one iteration of [1, Alg. 1]'s main loop, and `none` where the
abstraction error's fixed point was not reached. -/
noncomputable def NonlinearSys.abstrStep (sys : NonlinearSys n m) (U : S m)
    (lin : Vec ℝ n → Vec ℝ m → Mat ℝ n n × Mat ℝ n m) (Φ : S n → S n → S n)
    (sub : S n → S n → Bool) (enlarge : S n → S n) (Δt : ℝ) (ηlin ηabs o fuel : ℕ)
    (s : NonlinearSys.AbstrState S n) : Option (NonlinearSys.AbstrState S n) :=
  let zs := sys.linPoint Δt s.R U                                 -- 3. linPoint, eq. (6)
  let AB := lin zs.1 zs.2                                         -- 4.-5. taylor, linSys
  let lsys := NonlinearSys.linearize AB.1                         -- 5. the linearized system
  let Ulin := linInput sys.f AB.1 AB.2 zs.1 zs.2 U                -- 5. w ⊞ B(U ⊖ u✱)
    (OfPoint.ofPoint (0 : Vec ℝ n))
  let Rlint := lsys.timePointStep Δt ηlin s.R Ulin                -- 6. linReach, eq. (10)
  let Rlinτ := (lsys.timeIntervalStep Δt ηlin s.R)                -- 6. linReach, eq. (12)
    ⊞ lsys.inputSolution Δt ηlin Ulin
  let Ψ₀ := OfPoint.ofPoint (0 : Vec ℝ n)                         -- 7. Ψ ← 0
  match abstrErrLoop sub enlarge (Φ Rlinτ) Ψ₀ fuel with           -- 8.-11. the do-while
  | none => none
  | some Ψ =>
    let Rabs := lsys.inputSolution Δt ηabs Ψ                       -- 12. abstrSol, eq. (8)
    let Rt := Rlint ⊞ Rabs                                         -- 13. R(t_{k+1})
    let Rτ := Rlinτ ⊞ Rabs                                         -- 14. R(τ_{k+1})
    some { t := s.t + Δt,                                          -- 16. t ← t + Δt, k ← k + 1
           R := Reduce.reduce Rt o, Rτ := Reduce.reduce Rτ o }     -- 15. red

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
