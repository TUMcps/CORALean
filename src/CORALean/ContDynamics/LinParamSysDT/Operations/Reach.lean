import CORALean.ContDynamics.LinParamSysDT.Definitions.ReachOptions
import CORALean.ContDynamics.LinParamSysDT.LinParamSysDT
import CORALean.ContDynamics.Reach.Definitions.InputParams

/-!
# Reachability of a discrete-time linear system with a set-valued matrix

`reach`, character for character `LinearSysDT.reach`'s recursion, with the
matrix set `sys.A` multiplied through `Mtimes` instead of a single matrix.
`Mtimes` already quantifies over a set of matrices (`mtimes_outer`'s `⋃`), so
the point-matrix case, `𝕄 := Mat 𝕋`, needs no class of its own — it is
`Mtimes (Mat 𝕋) S`, the instance `LinearSysDT.reach` already uses.

Params and options are CORA's, as in `LinearSysDT.reach`: the problem is a
`Reach.InputParams` counted in sampling periods (`ℕ`), the step count is
`tFinal - tStart`, and `ρ` comes from `LinParamSysDT.ReachOptions`.
-/

-- Authors:       Claude Sonnet 5
-- Written:       06-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Plus Reduce Mtimes

variable {n : ℕ} {𝕄 : ℕ → ℕ → Type} [∀ m n, ContSet (𝕄 m n) (Mat ℝ m n)]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes 𝕄 S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The reachable set at time `tFinal`, from initial set `R₀` at `tStart` under
inputs `U`, held at maximum order `o`, at a system matrix ranging over `sys.A`. -/
def LinParamSysDT.reach (sys : LinParamSysDT 𝕄 n)
    (params : Reach.InputParams (S n) (S n) ℕ) (options : LinParamSysDT.ReachOptions) : S n :=
  let R₀ := params.X₀                                               -- the paper's symbols
  let U := params.U
  let o := options.ρ
  let N := params.tFinal - params.tStart                           -- steps, in sampling periods
  let step := fun R => reduce (plus (mtimes sys.A R) U) o          -- R_{k+1} = reduce(A R_k ⊕ U, o)
  Nat.repeat step N R₀                                              -- R_N

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
