module

public import CORALean.ContDynamics.NonlinearSys.Operations.AdaptStep

@[expose] public section

/-!
# `Alg. 2`, iterated

`adaptRun`: iterate [1, Alg. 2] while `t_k < t_end`, as `Alg. 1`'s line 2 does.

## Inputs
* `sys` – system
* `U` – input set
* `lin` – linearization at a point
* `Φ` – true-error map
* `sub` – containment test
* `enlarge` – enlargement of the applied error
* `le` – comparison of reals
* `rad` – radius of a set
* `dbox` – box widths of a set
* `ζδ` – first tuning constant
* `ζh` – second tuning constant
* `ζZ` – third tuning constant
* `ζK` – fourth tuning constant
* `tend` – end time
* `ηlin` – Taylor order of the linearization
* `ηabs` – Taylor order of the abstraction error
* `o` – zonotope order
* `fuel` – iteration bound
* `s₀` – initial loop state

## Output
* the loop state after each number of iterations, or none

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive Reachability Algorithms for
      Nonlinear Systems Using Abstraction Error Analysis". Nonlinear Analysis: Hybrid Systems, 2022.
-/

-- Authors:       Claude Sonnet 5
-- Written:       18-September-2026
-- Last update:   14-October-2026
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
variable [∀ n, OfPoint (S n) (Vec ℝ n)] [∀ n, Recenter (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S] [Real.OfInterval S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Iterate [1, Alg. 2] while `t_k < t_end`, as `Alg. 1`'s line 2 does. -/
noncomputable def NonlinearSys.adaptRun (sys : NonlinearSys n m) (U : S m)
    (lin : Vec ℝ n → Vec ℝ m → Mat ℝ n n × Mat ℝ n m) (Φ : ℕ → S n → S n → S n)
    (sub : S n → S n → Bool) (enlarge : S n → S n) (le : ℝ → ℝ → Bool) (rad : S n → ℝ)
    (dbox : S n → Fin n → ℝ) (ζδ ζh ζZ ζK tend : ℝ) (ηlin ηabs o fuel : ℕ)
    (s₀ : NonlinearSys.AdaptState S n) : ℕ → Option (NonlinearSys.AdaptState S n)
  | 0 => some s₀
  | k + 1 =>
    match sys.adaptRun U lin Φ sub enlarge le rad dbox ζδ ζh ζZ ζK tend ηlin ηabs o fuel s₀ k with
    | none => none
    | some s =>
      -- 2. `while t_k < t_end`, the horizon of Alg. 1
      if s.t < tend
      then sys.adaptStep U lin Φ sub enlarge le rad dbox ζδ ζh ζZ ζK ηlin ηabs o fuel s
      else some s

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
