import CORALean.ContDynamics.LinearSysDT.Definitions.ReachOptions
import CORALean.ContDynamics.LinearSysDT.LinearSysDT
import CORALean.ContDynamics.Reach.Definitions.InputParams

/-!
# Discrete-time linear systems: reachability

`reach` is written against `Plus` and `Reduce` alone, so it runs at a
representation with no `linComb`.

`reduce` is called once per step, at `o = options.zonotopeOrder`, kept positive
by `ReachOptions`. The result is the time-point set at `params.tFinal`, CORA's
last `timePoint.set`; `reachUnion` collects the earlier ones.

Time is counted in sampling periods: CORA's `linearSysDT` carries `dt` and takes
`(tFinal - tStart) / dt` steps, but no `dt` can be divided exactly at every scalar
this runs at — ℝ, where `discretize` holds `e^{AΔt}` exactly, has no computable
exact quotient — so `LinearSysDT` carries none, and `tStart`, `tFinal` are ℕ. The
step count `tFinal - tStart` is then exact, as CORA's integer check demands; a
horizon ending before it starts is `0` steps under ℕ's subtraction, where CORA
refuses it, and every guarantee here is stated at `tStart = 0`.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   30-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Plus Reduce Mtimes

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The reachable set at time `tFinal`, from initial set `R₀` at `tStart` under
inputs `U`, held at maximum order `o`. -/
def LinearSysDT.reach (sys : LinearSysDT 𝕋 n) (params : Reach.InputParams (S n) (S n) ℕ)
    (options : LinearSysDT.ReachOptions) : S n :=
  let R₀ := params.R0                                               -- the paper's symbols
  let U := params.U
  let o := options.zonotopeOrder
  let N := params.tFinal - params.tStart                           -- steps, in sampling periods
  let step := fun R => reduce (plus (mtimes sys.A R) U) o          -- R_{k+1} = reduce(A R_k ⊕ U, o)
  Nat.repeat step N R₀                                              -- R_N

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
