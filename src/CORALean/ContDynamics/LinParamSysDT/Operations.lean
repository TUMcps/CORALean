import CORALean.ContDynamics.LinParamSysDT.LinParamSysDT

/-!
# Reachability of a discrete-time linear system with a set-valued matrix

`reach`, character for character `LinearSysDT.reach`'s recursion, with the
matrix set `sys.A` multiplied through `Mtimes` instead of a single matrix.
`Mtimes` already quantifies over a set of matrices (`mtimes_outer`'s `⋃`), so
the point-matrix case, `𝕄 := Mat 𝕋`, needs no class of its own — it is
`Mtimes (Mat 𝕋) S`, the instance `LinearSysDT.reach` already uses.

`simulate` takes the matrix at each step as an argument, one point computation
per step chosen from `sys.A`, and carries no set instance of its own.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   06-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Plus Reduce Mtimes

variable {n : ℕ} {𝕄 : ℕ → ℕ → Type} [∀ m n, ContSet (𝕄 m n) (Mat ℝ m n)]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes 𝕄 S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The reachable set after `k` steps, from initial set `R₀` under inputs `U`,
held at maximum order `o`, at a system matrix ranging over `sys.A`. `ho` is
what rules out `o = 0`, exactly as in `LinearSysDT.reach`. -/
def LinParamSysDT.reach (sys : LinParamSysDT 𝕄 n) (o : ℕ) (ho : 0 < o) (R₀ U : S n) : ℕ → S n
  | 0 => R₀
  | k + 1 => reduce (plus (mtimes sys.A (sys.reach o ho R₀ U k)) U) o

omit [∀ m n, ContSet (𝕄 m n) (Mat ℝ m n)] [∀ n, ContSet (S n) (Vec ℝ n)]
    [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes 𝕄 S] in
/-- One sampled run of the dynamics from `x₀` under `u`, at a matrix `A k`
chosen per step — the concrete meaning of `step`'s `∃ A ∈ construct sys.A`;
not a field of `sys`, since it is chosen afresh each run. -/
def LinParamSysDT.simulate (sys : LinParamSysDT 𝕄 n) (A : ℕ → Mat ℝ n n)
    (x₀ : Vec ℝ n) (u : ℕ → Vec ℝ n) : ℕ → Vec ℝ n
  | 0 => x₀
  | k + 1 => A k *ᵥ sys.simulate A x₀ u k + u k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
