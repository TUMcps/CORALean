import CORALean.ContDynamics.LinParamSys.Definitions.WithInput
import CORALean.ContDynamics.LinParamSys.Operations.ParticularSolution
import CORALean.ContDynamics.LinParamSys.Operations.ReachStepk

/-!
# One window of `reachUnion` with inputs: the set over `τ_k = [t_k, t_k + Δt]`

`R(τ_k) = H^R(τ_k) ⊕ P^R(t_{k+1})`, [1, Alg. 4]'s window, `0 ∈ U`, laid out
as [1, Alg. 2]'s: the homogeneous set `reachStepk` carries to `τ_k`, plus
everything the input can have contributed by the window's right end, both at
every member of `sys.A`. One set serves the whole window because `0 ∈ U` makes
that contribution grow with time [1, Prop. 3.3].

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
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
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)] [Mtimes ℐ S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The window `τ_k = [k Δt, (k + 1) Δt]` at Taylor order `η`, inputs in
`sys.U`, at every member of `sys.A`: `R(τ_k) = H^R(τ_k) ⊕ P^R(t_{k+1})`. -/
noncomputable def LinParamSys.WithInput.reachStepk (sys : LinParamSys.WithInput S n) (Δt : ℝ)
    (η : ℕ) (X₀ : S n) (k : ℕ) : S n :=
  let HRτk := sys.sys.reachStepk Δt η X₀ k                       -- H^R(τ_k) = e^{[A] t_k} H^R(τ_0)
  let PRtk := sys.sys.particularSolution Δt η sys.U k            -- P^R(t_{k+1})
  Plus.plus HRτk PRtk                                            -- R(τ_k) = H^R(τ_k) ⊕ P^R(t_{k+1})

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
