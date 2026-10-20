module

public import CORALean.ContDynamics.LinearSys.Definitions.WithInputSplit
public import CORALean.ContDynamics.LinearSys.Operations.ConstInputSolution
public import CORALean.ContDynamics.LinearSys.Operations.ParticularSolution
public import CORALean.ContDynamics.LinearSys.Operations.StepInputConst
public import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalStep

@[expose] public section

/-!
# One window of `reach` with the input set split: the set over `τ_k`

[1, Alg. 3]'s window, `U = ũ ⊕ Ũ` by `Recenter`. The first window's
homogeneous set and the constant's contribution over it, `H^R(τ_0) ⊕ P̃^R(τ_0)`,
carried to `τ_k` by `e^{A t_k}`; plus `P̃(t_k) = ∫₀^{t_k} e^{Aσ}dσ ũ`, a point,
what the constant contributed before the window; plus `P^R(t_{k+1})` of `Ũ`,
Alg. 2's accumulated set, one set for the whole window since `0 ∈ Ũ`.
The paper subtracts `P̃(r)` from the first window and adds `P̃(t_{k+1})` back;
adding `P̃(t_k)` alone is the same sum without the subtraction.

## Inputs
* `sys` – linear system with split input
* `Δt` – step length
* `η` – Taylor order
* `X₀` – initial set
* `k` – window index

## Output
* set over the window with the split input

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
open Matrix ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [∀ n, OfPoint (S n) (Vec ℝ n)] [∀ n, Recenter (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The window `τ_k = [k Δt, (k + 1) Δt]` at Taylor order `η`, `U = ũ ⊕ Ũ`:
`R(τ_k) = e^{A t_k} (H^R(τ_0) ⊕ P̃^R(τ_0)) ⊕ P̃(t_k) ⊕ P^R_Ũ(t_{k+1})`. -/
noncomputable def LinearSys.WithInputSplit.reachStepk (sys : LinearSys.WithInputSplit 𝕋 S n)
    (Δt : ℝ) (η : ℕ) (X₀ : S n) (k : ℕ) : S n :=
  let uc := Recenter.center sys.U                                -- ũ, the constant
  let U₀ := Recenter.recenter sys.U                              -- Ũ = U - ũ, holding 0
  let tk := (k : ℝ) * Δt                                         -- t_k = k Δt
  let HRτ₀ := sys.sys.timeIntervalStep Δt η X₀                   -- H^R(τ_0)
  let PcRτ₀ : S n := sys.sys.constInputSolution Δt η uc          -- P̃^R(τ_0), ũ over τ_0
  let eAtk := exp (tk • toRealMat sys.sys.A)                     -- e^{A t_k}
  let Pctk : S n := OfPoint.ofPoint (sys.sys.stepInputConst uc tk)  -- P̃(t_k)
  let PRtk := sys.sys.particularSolution Δt η U₀ k               -- P^R_Ũ(t_{k+1})
  let Hτk := Mtimes.mtimes eAtk (Plus.plus HRτ₀ PcRτ₀)           -- e^{A t_k}(H^R ⊕ P̃^R)(τ_0)
  Plus.plus (Plus.plus Hτk Pctk) PRtk                            -- R(τ_k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
