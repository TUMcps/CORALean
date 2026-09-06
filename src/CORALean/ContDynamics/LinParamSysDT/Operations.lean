import CORALean.ContDynamics.LinParamSysDT.LinParamSysDT

/-!
# Reachability of a discrete-time linear system with a set-valued matrix

`reach`, character for character `LinearSysDT.reach`'s recursion, with the
matrix set `sys.A` multiplied through `Mtimes` instead of a single matrix.
`Mtimes` already quantifies over a set of matrices (`mtimes_outer`'s `⋃`), so
the point-matrix case, `𝕄 := Mat 𝕋`, needs no class of its own — it is
`Mtimes (Mat 𝕋) S`, the instance `LinearSysDT.reach` already uses.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet Plus Reduce Mtimes

variable {n : ℕ} {𝕄 : ℕ → ℕ → Type} [∀ m n, ContSet (𝕄 m n) (Mat ℝ m n)]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes 𝕄 S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The reachable set after `k` steps, from initial set `R₀` under inputs `U`,
held at maximum order `o`, at a system matrix ranging over `sys.A`. -/
def LinParamSysDT.reach (sys : LinParamSysDT 𝕄 n) (o : ℕ) (R₀ U : S n) : ℕ → S n
  | 0 => R₀
  | k + 1 => reduce (plus (mtimes sys.A (sys.reach o R₀ U k)) U) o

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
