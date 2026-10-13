module

public import CORALean.ContDynamics.NonlinearSys.NonlinearSys

@[expose] public section

/-!
# CORA's `options` for the adaptive abstraction algorithms

One record for `abstrReach` and `centreAbstrReach`, whose arguments coincide. CORA's
options where CORA has one, under the paper's names (`timeStep`, `taylorTerms`,
`zonotopeOrder`): `Δt`, the step the loop starts from; `η`,
the order of the linearized system's own enclosures (the paper's `η_lin`);
`ρ`, the order every set is reduced to.

The rest is not CORA's. `taylorTermsAbstr` is `η_abs`, the order the abstraction
error's input solution is taken at, where CORA uses `η` for both. `lin`
stands for what `taylor` and line 3 compute and nothing in this tree does; `Φ`, `sub`
and `enlarge` are the abstraction-error loop's; `fuel` bounds its do-while, which
has no stated iteration count; `K` is how many iterations `reach` unions. Each is
the caller's stand-in for something CORA computes or loops on, and each keeps the
paper's symbol.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       30-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet


-- ========================================  MAIN TYPE  ========================================= --

/-- The options of `NonlinearSys.abstrReach` and `NonlinearSys.centreAbstrReach`. -/
structure NonlinearSys.AbstrReachOptions (S : ℕ → Type) (n m : ℕ) where
  Δt : ℝ
  η : ℕ
  taylorTermsAbstr : ℕ
  ρ : ℕ
  lin : Vec ℝ n → Vec ℝ m → Mat ℝ n n × Mat ℝ n m
  Φ : S n → S n → S n
  sub : S n → S n → Bool
  enlarge : S n → S n
  fuel : ℕ
  K : ℕ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
