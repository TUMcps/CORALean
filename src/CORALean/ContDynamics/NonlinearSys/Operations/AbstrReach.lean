import CORALean.ContDynamics.NonlinearSys.Operations.AbstrRun

/-!
# `Alg. 1` line 18: the reachable set

`abstrReach`: `R([0,t_end])`, the union of the first `K` iterations'
time-interval sets. Line 18 unions the steps' sets, which is no zonotope, so
this is a `Set`.

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

/-- [1, Alg. 1] line 18: `R([0,t_end])`, the union of the first `K` iterations'
time-interval sets. -/
noncomputable def NonlinearSys.abstrReach (sys : NonlinearSys n m) (U : S m)
    (lin : Vec ℝ n → Vec ℝ m → Mat ℝ n n × Mat ℝ n m) (Φ : S n → S n → S n)
    (sub : S n → S n → Bool) (enlarge : S n → S n) (Δt tend : ℝ) (ηlin ηabs o fuel K : ℕ)
    (X₀ : S n) : Set (Vec ℝ n) :=
  ⋃ j < K, ⋃ s ∈ sys.abstrRun U lin Φ sub enlarge Δt tend ηlin ηabs o fuel X₀ (j + 1),
    construct s.Rτ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
