module

public import CORALean.ContDynamics.LinParamSys.Operations.ConstInputSolutionFloat
public import CORALean.ContDynamics.LinParamSys.Operations.ExpIntervalFloat

@[expose] public section

/-!
# What a constant input contributes up to the start of a window at every member, in floats

`LinParamSys.constPropagate` computed in `𝕋`: `P̃(t_0) = {0}`, and
`P̃(t_{k+1}) = [e^{[A]Δt}] P̃(t_k) ⊕ P̃^R(τ_0)`, [1, Alg. 1]'s recursion. Every factor is the one
box `[e^{[A]Δt}]` of `expIntervalFloat`, enclosed at the order admissible for `Δt`; the
accumulated set is reduced to order `ρ`.

## References

* [1] M. Althoff, B. H. Krogh and O. Stursberg. "Analyzing Reachability of Linear
      Dynamic Systems with Parametric Uncertainties". In A. Rauh and E. Auer (eds.),
      Modeling, Design, and Simulation of Systems with Uncertainties, Springer, 2011.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `P̃(t_k)` at index `k`, at every member of `sys.A`: `P̃(t_0) = {0}`, and
`P̃(t_{k+1}) = [e^{[A]Δt}] P̃(t_k) ⊕ P̃^R(τ_0)`, reduced to order `ρ`. -/
def LinParamSys.constPropagateFloat (sys : LinParamSys ℐ[𝕋] n)
    (Δt : 𝕋) (η ρ : ℕ) (uc : Vec 𝕋 n) : ℕ → Zonotope (Vec 𝕋 n)
  | 0 => OfScalarPoint.ofVec (S := 𝒵[𝕋])  -- P̃(t_0) = {0}
    (fun _ => (zero : 𝕋))
  | k + 1 =>
    let Pctk := sys.constPropagateFloat Δt η ρ uc k                  -- P̃(t_k)
    let eAΔt := sys.expIntervalFloat Δt Δt η                         -- [e^{[A]Δt}]
    let PcRΔt := sys.constInputSolutionFloat Δt η uc                 -- P̃^R(τ_0), ũ over one window
    Reduce.reduce (Mtimes.mtimes (𝕄 := ℐ[𝕋])
      (S := 𝒵[𝕋]) eAΔt Pctk ⊞ PcRΔt) ρ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
