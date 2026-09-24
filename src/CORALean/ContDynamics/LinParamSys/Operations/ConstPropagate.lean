import CORALean.ContDynamics.LinParamSys.Operations.ConstInputSolution
import CORALean.ContDynamics.LinParamSys.Operations.ExpEnclosure

/-!
# What a constant input contributes up to the start of a window, at every member

[1, Alg. 4]'s split case, off the first window: `particularSolution`'s own
recursion ([1, Prop. 3.2]'s), at the constant `ũ` in place of a set `U` holding
the origin. `P̃(t_0) = {0}`, and `P̃(t_{k+1}) = e^{[A]Δt} P̃(t_k) ⊕ P̃^R(τ_0)`,
`expIntegral_add_mulVec` carrying `∫₀^{t_k} e^{Aσ}dσ ũ` across one more window
of width `Δt` rather than across `t_k` itself, so every factor is enclosed at
the fixed order admissible for `Δt` alone.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open ContSet

variable {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [∀ n, OfPoint (S n) (Vec ℝ n)] [Mtimes ℐ S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `P̃(t_k)` at index `k`, at every member of `sys.A`: `P̃(t_0) = {0}`, and
`P̃(t_{k+1}) = e^{[A]Δt} P̃(t_k) ⊕ P̃^R(τ_0)`, `ũ` over one window `[0, Δt]`. -/
noncomputable def LinParamSys.constPropagate (sys : LinParamSys ℐ n) (Δt : ℝ) (η : ℕ)
    (uc : Vec ℝ n) : ℕ → S n
  | 0 => OfPoint.ofPoint (0 : Vec ℝ n)                            -- P̃(t_0) = {0}
  | k + 1 =>
    let Pctk := sys.constPropagate Δt η uc k                     -- P̃(t_k)
    let eAΔt := sys.expEnclosure Δt η                            -- e^{[A]Δt}
    let PcRΔt : S n := sys.constInputSolution Δt η uc            -- P̃^R(τ_0), ũ over one window
    Plus.plus (Mtimes.mtimes (𝕄 := ℐ) eAΔt Pctk) PcRΔt          -- P̃(t_{k+1})

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
