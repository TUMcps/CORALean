module

public import CORALean.ContDynamics.LinParamSys.Operations.ConstPropagate
public import CORALean.ContDynamics.LinParamSys.Operations.ParticularSolution
public import CORALean.ContDynamics.LinParamSys.Operations.ReachStepk

@[expose] public section

/-!
# One window of `reachUnion`: the set over `τ_k = [t_k, t_k + Δt]`

`LinearSys.WithInputSplit.reachStepk` at [1, Alg. 4]'s set of matrices. `V = B U ⊕ c` is the
input set in state coordinates, the `inputSet` that `reachUnion` computes once, split at its
stored centre `ũ` and `Ũ = V - ũ ∋ 0` by `Recentre`:
`R(τ_k) = e^{[A]t_k}(H^R(τ_0) ⊕ P̃^R(τ_0)) ⊕ P̃(t_k) ⊕ P^R_Ũ(t_{k+1})`.
`P̃(t_k)` is `constPropagate`, carried by `e^{[A]Δt}` one window at a time rather than by
`e^{[A]t_k}` itself, since no point value of it is available once `A` ranges over a set.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
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
variable [∀ n, OfPoint (S n) (Vec ℝ n)] [∀ n, Recentre (S n) (Vec ℝ n)] [Mtimes ℐ S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The window `τ_k = [k Δt, (k + 1) Δt]` at Taylor order `η`, the input set `V` of the state
space split at its centre, at every member of `sys.A`. -/
noncomputable def LinParamSys.reachStepkInput (sys : LinParamSys ℐ n)
    (Δt : ℝ) (η : ℕ) (X₀ : S n) (V : S n) (k : ℕ) : S n :=
  let uc := Recentre.centre V                                     -- ũ, the constant
  let U₀ := Recentre.recentre V                                    -- Ũ = V - ũ, holding 0
  let tk := (k : ℝ) * Δt                                           -- t_k = k Δt
  let HRτ₀ := sys.timeIntervalStep Δt η X₀                         -- H^R(τ_0)
  let PcRτ₀ : S n := sys.constInputSolution Δt η uc                -- P̃^R(τ_0), ũ over τ_0
  let eAtk := sys.expEnclosure tk η                                -- e^{[A]t_k}
  let Pctk : S n := sys.constPropagate Δt η uc k                   -- P̃(t_k)
  let PRtk := sys.particularSolution Δt η U₀ k                     -- P^R_Ũ(t_{k+1})
  let Hτk := Mtimes.mtimes (𝕄 := ℐ) eAtk (Plus.plus HRτ₀ PcRτ₀)    -- e^{[A]t_k}(H^R ⊕ P̃^R)(τ_0)
  Plus.plus (Plus.plus Hτk Pctk) PRtk                              -- R(τ_k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
