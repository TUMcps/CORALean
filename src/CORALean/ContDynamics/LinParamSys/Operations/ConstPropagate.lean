module

public import CORALean.ContDynamics.LinParamSys.Operations.ConstInputSolution
public import CORALean.ContDynamics.LinParamSys.Operations.ExpEnclosure

@[expose] public section

/-!
# What a constant input contributes up to the start of a window, at every member

The split case of [1, Alg. 1] (an input set missing the origin, which [1, Sec. 3.3] leaves out), off
the first window: `particularSolution`'s own recursion ([1, Alg. 1]'s), at the constant `ũ` in place
of a set `U` holding the origin. `P̃(t_0) = {0}`, and `P̃(t_{k+1}) = e^{[A]Δt} P̃(t_k) ⊕ P̃^R(τ_0)`,
`expIntegral_add_mulVec` carrying `∫₀^{t_k} e^{Aσ}dσ ũ` across one more window
of width `Δt` rather than across `t_k` itself, so every factor is enclosed at
the fixed order admissible for `Δt` alone.

## Inputs
* `sys` – system
* `Δt` – window length
* `η` – Taylor order
* `uc` – constant input

## Output
* the contribution up to the start of each window, by window index

## References

* [1] [M. Althoff, B. H. Krogh and O. Stursberg. "Analyzing Reachability of Linear Dynamic Systems
      with Parametric Uncertainties". Modeling, Design, and Simulation of Systems with
      Uncertainties,
      2011.](../../../../../references/2011/althoff-reachability-parametric-uncertainties.md)
-/

-- Authors:       Claude Sonnet 5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open ContSet

variable {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [∀ n, OfPoint (S n) (Vec ℝ n)] [Mtimes ℐ S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `P̃(t_k)` at index `k`, at every member of `sys.A`: `P̃(t_0) = {0}`, and
`P̃(t_{k+1}) = e^{[A]Δt} P̃(t_k) ⊕ P̃^R(τ_0)`, `ũ` over one window `[0, Δt]`. -/
noncomputable def LinParamSys.constPropagate (sys : LinParamSys ℐ n) (Δt : ℝ) (η : ℕ)
    (uc : Vec ℝ n) : ℕ → S n
  | 0 => OfPoint.ofPoint (0 : Vec ℝ n)                            -- P̃(t_0) = {0}
  | k + 1 =>
    let Pctk := sys.constPropagate Δt η uc k                     -- P̃(t_k)
    let eAΔt := sys.expEnclosure Δt η                            -- e^{[A]Δt}
    let PcRΔt : S n := sys.constInputSolution Δt η uc            -- P̃^R(τ_0), ũ over one window
    Plus.plus (Mtimes.mtimes (𝕄 := ℐ) eAΔt Pctk) PcRΔt          -- P̃(t_{k+1})

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
