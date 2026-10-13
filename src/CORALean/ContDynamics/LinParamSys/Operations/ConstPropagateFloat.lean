import CORALean.ContDynamics.LinParamSys.Operations.ConstInputSolutionFloat
import CORALean.ContDynamics.LinParamSys.Operations.ExpIntervalFloat

/-!
# What a constant input contributes up to the start of a window at every member, in floats

`LinParamSys.constPropagate` computed in `𝕋`: `P̃(t_0) = {0}`, and
`P̃(t_{k+1}) = [e^{[A]Δt}] P̃(t_k) ⊕ P̃^R(τ_0)` [1, Prop. 3.2]. Every factor is the one box
`[e^{[A]Δt}]` of `expIntervalFloat`, enclosed at the order admissible for `Δt`; the
accumulated set is reduced to order `ρ`.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
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
def LinParamSys.constPropagateFloat (sys : LinParamSys (fun m n => Interval (Mat 𝕋 m n)) n)
    (Δt : 𝕋) (η ρ : ℕ) (uc : Vec 𝕋 n) : ℕ → Zonotope (Vec 𝕋 n)
  | 0 => OfScalarPoint.ofVec (S := fun k => Zonotope (Vec 𝕋 k))  -- P̃(t_0) = {0}
    (fun _ => (zero : 𝕋))
  | k + 1 =>
    let Pctk := sys.constPropagateFloat Δt η ρ uc k                  -- P̃(t_k)
    let eAΔt := sys.expIntervalFloat Δt Δt η                         -- [e^{[A]Δt}]
    let PcRΔt := sys.constInputSolutionFloat Δt η uc                 -- P̃^R(τ_0), ũ over one window
    Reduce.reduce (Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n))
      (S := fun k => Zonotope (Vec 𝕋 k)) eAΔt Pctk ⊞ PcRΔt) ρ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
