import CORALean.ContDynamics.NonlinearSys.Operations.CentreAbstrRun

/-!
# `Alg. 1` line 17, linearizing at the centre

`centreAbstrReach`: `R([0,t_K])`, the union of the first `K` iterations'
time-interval sets. Line 17's union is no zonotope, so this is a `Set`.

## References

* [1] M. Wetzlinger, A. Kulmburg and M. Althoff. "Adaptive Parameter Tuning for
      Reachability Analysis of Nonlinear Systems". HSCC, 2021, Article 16.
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

/-- [1, Alg. 1] line 17: `R([0,t_K])`, the union of the first `K` iterations'
time-interval sets. -/
noncomputable def NonlinearSys.centreAbstrReach (sys : NonlinearSys n m) (U : S m)
    (lin : Vec ℝ n → Vec ℝ m → Mat ℝ n n × Mat ℝ n m) (Φ : S n → S n → S n)
    (sub : S n → S n → Bool) (enlarge : S n → S n) (Δt tK : ℝ) (ηlin ηabs o fuel K : ℕ)
    (X₀ : S n) : Set (Vec ℝ n) :=
  ⋃ j < K, ⋃ s ∈ sys.centreAbstrRun U lin Φ sub enlarge Δt tK ηlin ηabs o fuel X₀ (j + 1),
    construct s.Rτ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
