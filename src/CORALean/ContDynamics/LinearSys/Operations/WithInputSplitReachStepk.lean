module

public import CORALean.ContDynamics.LinearSys.Definitions.WithInputSplit
public import CORALean.ContDynamics.LinearSys.Operations.ConstInputSolution
public import CORALean.ContDynamics.LinearSys.Operations.ParticularSolution
public import CORALean.ContDynamics.LinearSys.Operations.StepInputConst
public import CORALean.ContDynamics.LinearSys.Operations.TimeInterval

@[expose] public section

/-!
# One window of `reach` with the input set split: the set over `τ_k`

The input set split as [1, Eq. 4] splits it, `U = ũ ⊕ Ũ` by `Recenter`. [1, Eq. 4]'s first
window, the homogeneous set and the constant's contribution over it, `H^R(τ_0) ⊕ P̃^R(τ_0)`,
carried to `τ_k` by `e^{A t_k}`; plus `P̃(t_k) = ∫₀^{t_k} e^{Aσ}dσ ũ`, a point, what the constant
contributed before the window; plus `P^R(t_{k+1})` of `Ũ`, the accumulated set of
`WithInput.reachStepk`, one set for the whole window since `0 ∈ Ũ`.

## Inputs
* `sys` – linear system with split input
* `Δt` – step length
* `η` – Taylor order
* `X₀` – initial set
* `k` – window index

## Output
* set over the window with the split input

## References

* [1] M. Althoff and B. H. Krogh. "Reachability Analysis of Nonlinear Differential-Algebraic
      Systems". IEEE Transactions on Automatic Control, 59(2):371-383, 2014.
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
  let HRτ₀ := sys.sys.timeInterval Δt η X₀                   -- H^R(τ_0)
  let PcRτ₀ : S n := sys.sys.constInputSolution Δt η uc          -- P̃^R(τ_0), ũ over τ_0
  let eAtk := exp (tk • toRealMat sys.sys.A)                     -- e^{A t_k}
  let Pctk : S n := OfPoint.ofPoint (sys.sys.stepInputConst uc tk)  -- P̃(t_k)
  let PRtk := sys.sys.particularSolution Δt η U₀ k               -- P^R_Ũ(t_{k+1})
  let Hτk := Mtimes.mtimes eAtk (Plus.plus HRτ₀ PcRτ₀)           -- e^{A t_k}(H^R ⊕ P̃^R)(τ_0)
  Plus.plus (Plus.plus Hτk Pctk) PRtk                            -- R(τ_k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
