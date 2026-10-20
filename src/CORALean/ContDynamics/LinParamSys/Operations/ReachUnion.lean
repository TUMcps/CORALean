module

public import CORALean.ContDynamics.LinParamSys.Operations.ConstPropagate
public import CORALean.ContDynamics.LinParamSys.Operations.InputSet
public import CORALean.ContDynamics.LinParamSys.Operations.ParticularSolution
public import CORALean.ContDynamics.LinParamSys.Operations.ReachOrder
public import CORALean.ContDynamics.LinParamSys.Operations.ReachStepk
public import CORALean.ContDynamics.LinearSys.Definitions.ReachStepOptions
public import CORALean.ContDynamics.Reach.Definitions.InputParams
public import CORALean.ContSet.SetUnion.SetUnion

@[expose] public section

/-!
# Reachability with inputs over `[tStart, tFinal]`, one window of width `Δt` at a time

[1, Alg. 1]'s loop with CORA's `params.U`, in input coordinates, anywhere in the input space:
the windows `τ_0, …, τ_{N-1}`, one `aux_reachStepkInput` each, collected as a `SetUnion`,
`N = ⌈(tFinal - tStart) / Δt⌉` of them and never fewer than one. The state-space input set
`V = B U ⊕ c` is formed here, as CORA's `priv_inputSolution` forms it, and each window splits
it at its center, so `0 ∈ U` is not asked. No `box()` on the accumulated input set: that is a
reduction, which an enclosure need not make. `η = options.η` is raised to `reachOrder Δt + 2`
where that is higher: the enclosures hold only at an admissible order.

## Inputs
* `sys` – system
* `params` – reachability parameters with inputs
* `options` – reachability options

## Output
* one time-interval set per window, as a union

## References

* [1] M. Althoff, B. H. Krogh and O. Stursberg. "Analyzing Reachability of Linear
      Dynamic Systems with Parametric Uncertainties". In A. Rauh and E. Auer (eds.),
      Modeling, Design, and Simulation of Systems with Uncertainties, Springer, 2011.
-/

-- Authors:       Claude Sonnet 5, Claude Sonnet 5.5
-- Written:       24-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open ContSet

variable {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [∀ n, OfPoint (S n) (Vec ℝ n)] [∀ n, Recenter (S n) (Vec ℝ n)] [Mtimes ℐ S]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The window `τ_k = [k Δt, (k + 1) Δt]` at Taylor order `η`, the input set `V` of the state
space split at its center, at every member of `sys.A`. -/
noncomputable def LinParamSys.aux_reachStepkInput (sys : LinParamSys ℐ n)
    (Δt : ℝ) (η : ℕ) (X₀ : S n) (V : S n) (k : ℕ) : S n :=
  let uc := Recenter.center V                                     -- ũ, the constant
  let U₀ := Recenter.recenter V                                    -- Ũ = V - ũ, holding 0
  let tk := (k : ℝ) * Δt                                           -- t_k = k Δt
  let HRτ₀ := sys.timeIntervalStep Δt η X₀                         -- H^R(τ_0)
  let PcRτ₀ : S n := sys.constInputSolution Δt η uc                -- P̃^R(τ_0), ũ over τ_0
  let eAtk := sys.expEnclosure tk η                                -- e^{[A]t_k}
  let Pctk : S n := sys.constPropagate Δt η uc k                   -- P̃(t_k)
  let PRtk := sys.particularSolution Δt η U₀ k                     -- P^R_Ũ(t_{k+1})
  let Hτk := Mtimes.mtimes (𝕄 := ℐ) eAtk (Plus.plus HRτ₀ PcRτ₀)    -- e^{[A]t_k}(H^R ⊕ P̃^R)(τ_0)
  Plus.plus (Plus.plus Hτk Pctk) PRtk                              -- R(τ_k)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- One time-interval set per window `τ_k`, `k < ⌈(tFinal - tStart) / Δt⌉` (at least one),
under inputs `params.U` in input coordinates, at order `η` raised until admissible. -/
noncomputable def LinParamSys.reachUnion (sys : LinParamSys ℐ n)
    (params : Reach.InputParams (S n) (S sys.m) ℝ) (options : LinearSys.ReachStepOptions ℝ) :
    SetUnion (S n) :=
  let X₀ := params.X₀                                             -- the paper's symbols
  let Δt := options.Δt
  let N := max 1 ⌈(params.tFinal - params.tStart) / Δt⌉₊         -- windows τ_0, …, τ_{N-1}
  let η' := max options.η (sys.reachOrder Δt + 2)                 -- η, raised until admissible
  let V := sys.inputSet params.U                                  -- V = B U ⊕ c, in the state space
  ⟨(List.range N).map (sys.aux_reachStepkInput Δt η' X₀ V)⟩           -- ⋃_{k < N} R(τ_k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
