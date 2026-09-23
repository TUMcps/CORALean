import CORALean.ContDynamics.NonlinearSys.Operations.AbstrInit
import CORALean.ContDynamics.NonlinearSys.Operations.AbstrStep

/-!
# `Alg. 1` lines 2 and 17: the loop

`abstrRun`: [1, Alg. 1] lines 2 and 17, iterate the step while `t_k < t_end`.
Line 2's `while` is no Lean recursion, so the caller supplies the iteration
count and a run that has reached `t_end` stands still, and a step that gave
out propagates as `none`.

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive
      Reachability Algorithms for Nonlinear Systems Using Abstraction Error
      Analysis". Nonlinear Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
-/

-- Authors:       Tobias Ladner
-- Written:       18-September-2026
-- Last update:   ---
-- Last revision: ---


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

/-- Lines 2-17: iterate the step while `t_k < t_end`. -/
noncomputable def NonlinearSys.abstrRun (sys : NonlinearSys n m) (U : S m)
    (lin : Vec ℝ n → Vec ℝ m → Mat ℝ n n × Mat ℝ n m) (Φ : S n → S n → S n)
    (sub : S n → S n → Bool) (enlarge : S n → S n) (Δt tend : ℝ) (ηlin ηabs o fuel : ℕ)
    (X₀ : S n) : ℕ → Option (NonlinearSys.AbstrState S n)
  | 0 => some (NonlinearSys.abstrInit X₀)                          -- 1. initialize
  | k + 1 =>
    match sys.abstrRun U lin Φ sub enlarge Δt tend ηlin ηabs o fuel X₀ k with
    | none => none
    | some s =>
      if s.t < tend                                                -- 2. while t_k < t_end
      then sys.abstrStep U lin Φ sub enlarge Δt ηlin ηabs o fuel s
      else some s

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
