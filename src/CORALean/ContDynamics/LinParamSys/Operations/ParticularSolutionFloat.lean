module

public import CORALean.ContDynamics.LinParamSys.Operations.InputSolutionFloat
public import CORALean.ContDynamics.LinParamSys.Operations.ReachStepkFloat

@[expose] public section

/-!
# The input's contribution up to the end of a window at every member, in floats

`LinParamSys.particularSolution` computed in `𝕋`: `P^R(t_{k+1})` grown one window
at a time from `P^R(Δt)`, `inputSolutionFloat`'s set, as
`P^R(t_{k+1}) = P^R(t_k) ⊕ [e^{[A] t_k}] P^R(Δt)` [1, Prop. 3.2]. The new window
is `reachStepkFloat` applied to `P^R(Δt)`, so it encloses `e^{[A] t_k}` by scaling
and squaring there, and no window is found when that has no admissible
squaring count. The accumulated set is reduced to order `ρ`.

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

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `P^R(t_{k+1})` at index `k`, at every member of `sys.A`: `P^R(t_1) = P^R(Δt)`, and
`P^R(t_{k+2}) = P^R(t_{k+1}) ⊕ [e^{[A] t_{k+1}}] P^R(Δt)`, reduced to order `ρ`. -/
def LinParamSys.particularSolutionFloat (sys : LinParamSys (fun m n => Interval (Mat 𝕋 m n)) n)
    (Δt : 𝕋) (η ρ : ℕ) (U : Zonotope (Vec 𝕋 n)) : ℕ → Option (Zonotope (Vec 𝕋 n))
  | 0 => some (sys.inputSolutionFloat Δt η U)                    -- P^R(t_1) = P^R(Δt)
  | k + 1 => do
    let PRtk ← sys.particularSolutionFloat Δt η ρ U k            -- P^R(t_{k+1})
    let PRΔt := sys.inputSolutionFloat Δt η U                    -- P^R(Δt)
    let eAtkPRΔt ← sys.reachStepkFloat Δt η PRΔt (k + 1)         -- [e^{[A] t_{k+1}}] P^R(Δt)
    pure (Reduce.reduce (PRtk ⊞ eAtkPRΔt) ρ)                     -- P^R(t_{k+2})

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
