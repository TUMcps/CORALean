import CORALean.ContDynamics.LinParamSys.Definitions.WithInputSplit
import CORALean.ContDynamics.LinParamSys.Operations.ConstPropagate
import CORALean.ContDynamics.LinParamSys.Operations.ParticularSolution
import CORALean.ContDynamics.LinParamSys.Operations.ReachStepk

/-!
# One window of `reachUnion` with the input set split: the set over `τ_k`

`LinearSys.WithInputSplit.reachStepk` at [1, Alg. 4]'s set of matrices,
`U = ũ ⊕ Ũ` by `Recentre`:
`R(τ_k) = e^{[A]t_k}(H^R(τ_0) ⊕ P̃^R(τ_0)) ⊕ P̃(t_k) ⊕ P^R_Ũ(t_{k+1})`.
`P̃(t_k)` is `constPropagate`, carried by `e^{[A]Δt}` one window at a time
rather than by `e^{[A]t_k}` itself, since no point value of it is available
once `A` ranges over a set.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
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
variable [∀ n, OfPoint (S n) (Vec ℝ n)] [∀ n, Recentre (S n) (Vec ℝ n)] [Mtimes ℐ S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The window `τ_k = [k Δt, (k + 1) Δt]` at Taylor order `η`, `U = ũ ⊕ Ũ`, at
every member of `sys.A`:
`R(τ_k) = e^{[A]t_k}(H^R(τ_0) ⊕ P̃^R(τ_0)) ⊕ P̃(t_k) ⊕ P^R_Ũ(t_{k+1})`. -/
noncomputable def LinParamSys.WithInputSplit.reachStepk (sys : LinParamSys.WithInputSplit S n)
    (Δt : ℝ) (η : ℕ) (X₀ : S n) (k : ℕ) : S n :=
  let uc := Recentre.centre sys.U                                -- ũ, the constant
  let U₀ := Recentre.recentre sys.U                               -- Ũ = U - ũ, holding 0
  let tk := (k : ℝ) * Δt                                          -- t_k = k Δt
  let HRτ₀ := sys.sys.timeIntervalStep Δt η X₀                    -- H^R(τ_0)
  let PcRτ₀ : S n := sys.sys.constInputSolution Δt η uc           -- P̃^R(τ_0), ũ over τ_0
  let eAtk := sys.sys.expEnclosure tk η                           -- e^{[A]t_k}
  let Pctk : S n := sys.sys.constPropagate Δt η uc k              -- P̃(t_k)
  let PRtk := sys.sys.particularSolution Δt η U₀ k                -- P^R_Ũ(t_{k+1})
  let Hτk := Mtimes.mtimes (𝕄 := ℐ) eAtk (Plus.plus HRτ₀ PcRτ₀)   -- e^{[A]t_k}(H^R ⊕ P̃^R)(τ_0)
  Plus.plus (Plus.plus Hτk Pctk) PRtk                             -- R(τ_k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
