import CORALean.ContSet.ContSet.ContSet

/-!
# Continuous-time nonlinear systems with uncertain parameters

CORA's `nonlinParamSys`: `ẋ(t) = f(x(t), u(t), p(t))`, `NonlinearSys` with a third
argument ranging over a parameter set — the last of the main system classes with
no counterpart here.

Two trajectory readings, as CORA distinguishes them: `Trajectory` lets `p` vary
freely over time, a fresh element of `P` at every instant, mirroring
`LinParamSysDT.Trajectory`'s fresh system matrix each step; `ConstTrajectory`
fixes one `p ∈ construct P` for the whole run, the uncertain-but-constant
reading. Every constant trajectory is a time-varying one,
`constTrajectory_toTrajectory` below; the converse fails — a time-varying
trajectory need not hold at any single `p` — but is not stated here, no
counterexample having been constructed.

`NonlinearSys.toNonlinParam` and `NonlinParamSys.toNonlinearSys`, in
`Theorems/`, are the two embeddings: ignoring the parameter, and reading it as
an extra input.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet

variable {n m q : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ========================================  MAIN TYPE  ========================================= --

structure NonlinParamSys (n m q : ℕ) where
  f : Vec ℝ n → Vec ℝ m → Vec ℝ q → Vec ℝ n

structure NonlinParamSys.Trajectory (sys : NonlinParamSys n m q) (T : Set ℝ)
    (R₀ : S n) (U : S m) (P : S q) (x : ℝ → Vec ℝ n) (u : ℝ → Vec ℝ m)
    (p : ℝ → Vec ℝ q) : Prop where
  init : x 0 ∈ construct R₀
  input (t : ℝ) (ht : t ∈ T) : u t ∈ construct U
  param (t : ℝ) (ht : t ∈ T) : p t ∈ construct P
  flow (t : ℝ) (ht : t ∈ T) : HasDerivWithinAt x (sys.f (x t) (u t) (p t)) T t

/-- The uncertain-but-constant reading: one `p ∈ construct P` for the whole run,
rather than a fresh one at every instant. -/
structure NonlinParamSys.ConstTrajectory (sys : NonlinParamSys n m q) (T : Set ℝ)
    (R₀ : S n) (U : S m) (P : S q) (x : ℝ → Vec ℝ n) (u : ℝ → Vec ℝ m)
    (p : Vec ℝ q) : Prop where
  init : x 0 ∈ construct R₀
  input (t : ℝ) (ht : t ∈ T) : u t ∈ construct U
  param : p ∈ construct P
  flow (t : ℝ) (ht : t ∈ T) : HasDerivWithinAt x (sys.f (x t) (u t) p) T t

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
