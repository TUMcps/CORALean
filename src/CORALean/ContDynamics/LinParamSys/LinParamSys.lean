import CORALean.ContSet.ContSet.ContSet

/-!
# Continuous-time linear systems with a set-valued system matrix

CORA's `@linParamSys`, `ẋ(t) = A x(t) + u(t)` with `A` ranging over a set
`sys.A` — the system-matrix uncertainty CORA calls `type`. `Trajectory` is
`'varParam'`: a fresh `A t ∈ construct sys.A` at every instant. `ConstTrajectory`
is `'constParam'` (CORA's default): one `A ∈ construct sys.A`, fixed over the
whole flow. `constTrajectory_toTrajectory` is the direction that always holds —
a constant run is a time-varying one at the constant function; the converse
fails (a run free to vary need not settle on one matrix) and is not stated,
having no counterexample constructed here.

`B` and `c` are absent, as in `LinearSys`: `B U ⊕ c` folds into the input set by
one `mtimes` and one `plus`, and unifying that fold for both classes at once is
#59, not done here.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet

variable {n : ℕ} {𝕄 : ℕ → ℕ → Type} [∀ m n, ContSet (𝕄 m n) (Mat ℝ m n)]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ========================================  MAIN TYPE  ========================================= --

structure LinParamSys (𝕄 : ℕ → ℕ → Type) (n : ℕ) where
  A : 𝕄 n n

structure LinParamSys.Trajectory (sys : LinParamSys 𝕄 n) (T : Set ℝ) (R₀ U : S n)
    (x u : ℝ → Vec ℝ n) (A : ℝ → Mat ℝ n n) : Prop where
  init : x 0 ∈ construct R₀
  input (t : ℝ) (ht : t ∈ T) : u t ∈ construct U
  param (t : ℝ) (ht : t ∈ T) : A t ∈ construct sys.A
  flow (t : ℝ) (ht : t ∈ T) : HasDerivWithinAt x (A t *ᵥ x t + u t) T t

/-- `'constParam'`: one matrix `A`, fixed over the whole flow, rather than
`Trajectory`'s fresh `A t` at each instant. -/
structure LinParamSys.ConstTrajectory (sys : LinParamSys 𝕄 n) (T : Set ℝ) (R₀ U : S n)
    (x u : ℝ → Vec ℝ n) (A : Mat ℝ n n) : Prop where
  init : x 0 ∈ construct R₀
  input (t : ℝ) (ht : t ∈ T) : u t ∈ construct U
  param : A ∈ construct sys.A
  flow (t : ℝ) (ht : t ∈ T) : HasDerivWithinAt x (A *ᵥ x t + u t) T t

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
