module

public import CORALean.ContDynamics.LinParamSys.Operations.ExpEnclosure
public import CORALean.ContDynamics.LinParamSys.Operations.InputSolution

@[expose] public section

/-!
# The input's contribution up to the end of a window, at every member

`LinearSys.particularSolution` at a set of matrices: `P^R(t_{k+1})`, grown one
window at a time from `P^R(Δt)`, `inputSolution`'s set, as
`P^R(t_{k+1}) = P^R(t_k) ⊕ e^{[A] t_k} P^R(Δt)`, [1, Alg. 1]'s
`R_k = M(r) R_{k-1} + P_0` unrolled with the new window prepended, with `e^{[A] t_k}` the interval
matrix `expEnclosure`. Indexed from `0`, so that `P^R(t_0) = {0}` never has to be represented.

## References

* [1] M. Althoff, B. H. Krogh and O. Stursberg. "Analyzing Reachability of Linear
      Dynamic Systems with Parametric Uncertainties". In A. Rauh and E. Auer (eds.),
      Modeling, Design, and Simulation of Systems with Uncertainties, Springer, 2011.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open ContSet

variable {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes ℐ S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `P^R(t_{k+1})` at index `k`, at every member of `sys.A`: `P^R(t_1) = P^R(Δt)`,
and `P^R(t_{k+2}) = P^R(t_{k+1}) ⊕ e^{[A] t_{k+1}} P^R(Δt)`. -/
noncomputable def LinParamSys.particularSolution (sys : LinParamSys ℐ n) (Δt : ℝ) (η : ℕ)
    (U : S n) : ℕ → S n
  | 0 => sys.inputSolution Δt η U                               -- P^R(t_1) = P^R(Δt)
  | k + 1 =>
    let PRtk := sys.particularSolution Δt η U k                -- P^R(t_{k+1})
    let tk := ((k + 1 : ℕ) : ℝ) * Δt                            -- t_{k+1}
    let PRΔt := sys.inputSolution Δt η U                        -- P^R(Δt)
    let eAtk := sys.expEnclosure tk η                           -- e^{[A] t_{k+1}}
    Plus.plus PRtk (Mtimes.mtimes (𝕄 := ℐ) eAtk PRΔt)          -- P^R(t_{k+2})

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
