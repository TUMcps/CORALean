import CORALean.ContDynamics.LinParamSys.Operations.ParticularSolutionFloat
import CORALean.ContDynamics.LinParamSys.Operations.ReachStepkFloat

/-!
# One window with inputs at every member, in floats

`LinParamSys.WithInput.reachStepk` computed in `𝕋`, `0 ∈ U`, as [1, Alg. 4] reads it:
`R(τ_k) = H^R(τ_k) ⊕ P^R(t_{k+1})`, the homogeneous window `reachStepkFloat` carries
to `τ_k`, plus everything the input can have contributed by the window's right end,
`particularSolutionFloat`. No window when either has none.

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

/-- The window `τ_k = [k Δt, (k + 1) Δt]` from the first one `Rτ₀`, inputs in `U`,
at every member of `sys.A`: `R(τ_k) = H^R(τ_k) ⊕ P^R(t_{k+1})`. -/
def LinParamSys.reachStepkFloatInput (sys : LinParamSys (fun m n => Interval (Mat 𝕋 m n)) n)
    (U : Zonotope (Vec 𝕋 n)) (ρ : ℕ) (Δt : 𝕋) (η : ℕ) (Rτ₀ : Zonotope (Vec 𝕋 n)) (k : ℕ) :
    Option (Zonotope (Vec 𝕋 n)) := do
  let HRτk ← sys.reachStepkFloat Δt η Rτ₀ k                  -- H^R(τ_k) = [e^{[A] t_k}] H^R(τ_0)
  let PRtk ← sys.particularSolutionFloat Δt η ρ U k          -- P^R(t_{k+1})
  pure (HRτk ⊞ PRtk)                                          -- R(τ_k) = H^R(τ_k) ⊕ P^R(t_{k+1})

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
