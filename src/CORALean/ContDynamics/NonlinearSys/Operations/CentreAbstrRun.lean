module

public import CORALean.ContDynamics.NonlinearSys.Operations.CentreAbstrInit
public import CORALean.ContDynamics.NonlinearSys.Operations.CentreAbstrStep

@[expose] public section

/-!
# `Alg. 1` lines 2 and 16, linearizing at the centre

`centreAbstrRun`: [1, Alg. 1] lines 2 and 16, iterate the step while
`t_s < t_K`. Line 2's `while` is no Lean recursion, so the caller supplies
the iteration count and a run past `t_K` stands still, and a step that gave
out propagates as `none`.

## References

* [1] M. Wetzlinger, A. Kulmburg and M. Althoff. "Adaptive Parameter Tuning for
      Reachability Analysis of Nonlinear Systems". HSCC, 2021, Article 16.
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

/-- Lines 2-16: iterate the step while `t_s < t_K`. -/
noncomputable def NonlinearSys.centreAbstrRun (sys : NonlinearSys n m) (U : S m)
    (lin : Vec ℝ n → Vec ℝ m → Mat ℝ n n × Mat ℝ n m) (Φ : S n → S n → S n)
    (sub : S n → S n → Bool) (enlarge : S n → S n) (Δt tK : ℝ) (ηlin ηabs o fuel : ℕ)
    (X₀ : S n) : ℕ → Option (NonlinearSys.CentreAbstrState S n)
  | 0 => some (NonlinearSys.centreAbstrInit X₀)                    -- 1. initialize
  | k + 1 =>
    match sys.centreAbstrRun U lin Φ sub enlarge Δt tK ηlin ηabs o fuel X₀ k with
    | none => none
    | some s =>
      if s.t < tK                                                  -- 2. while t_s < t_K
      then sys.centreAbstrStep U lin Φ sub enlarge Δt ηlin ηabs o fuel s
      else some s

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
