module

public import CORALean.ContDynamics.LinearSys.Definitions.WithInput
public import CORALean.ContDynamics.LinearSys.Operations.ParticularSolution
public import CORALean.ContDynamics.LinearSys.Operations.ReachStepkWrappingFree

@[expose] public section

/-!
# One window of `reach` with inputs: the set over `τ_k = [t_k, t_k + Δt]`

`R(τ_k) = H^R(τ_k) ⊕ P^R(t_{k+1})`, [1, Alg. 2]'s window: the homogeneous set
`reachStepkWrappingFree` carries to `τ_k`, plus everything the input can have contributed
by the window's right end. One set serves every time of the window because
`0 ∈ U` makes that contribution grow with time [1, Prop. 3.3], so the right end
bounds every earlier instant.

## Inputs
* `sys` – linear system with input
* `Δt` – step length
* `η` – Taylor order
* `X₀` – initial set
* `k` – window index

## Output
* set over the window with the input

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

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The window `τ_k = [k Δt, (k + 1) Δt]` at Taylor order `η`, inputs in
`sys.U`: `R(τ_k) = H^R(τ_k) ⊕ P^R(t_{k+1})`. -/
noncomputable def LinearSys.WithInput.reachStepk (sys : LinearSys.WithInput 𝕋 S n) (Δt : ℝ)
    (η : ℕ) (X₀ : S n) (k : ℕ) : S n :=
  let HRτk := sys.sys.reachStepkWrappingFree Δt η X₀ k           -- H^R(τ_k) = e^{A t_k} H^R(τ_0)
  let PRtk := sys.sys.particularSolution Δt η sys.U k            -- P^R(t_{k+1})
  Plus.plus HRτk PRtk                                            -- R(τ_k) = H^R(τ_k) ⊕ P^R(t_{k+1})

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
