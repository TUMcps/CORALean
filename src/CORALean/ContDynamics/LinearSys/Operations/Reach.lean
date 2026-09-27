import CORALean.ContDynamics.LinearSys.Operations.ReachStepk
import CORALean.ContSet.SetUnion.SetUnion

/-!
# Reachability over `[0, tFinal]`, recursively, one window of width `Δt` at a time

The windows `τ_0, …, τ_{N-1}`, one `reachStepk` each, collected as a `SetUnion`:
`N = ⌈tFinal / Δt⌉` of them, so the last may overshoot `tFinal`, which an outer
enclosure may. CORA's `standard` scheme, its default: [1, Alg. 4] at a point
matrix, with no input and no order reduction.

Unlike `reachWrappingFree`, `η` is taken as given and `N` is not raised to one:
`reach_outer` asks for what `timeIntervalStep_outer` needs of the order, and for
`0 < tFinal`, instead.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       27-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- One time-interval set per window `τ_k`, `k < ⌈tFinal / Δt⌉`, at order `η`. -/
noncomputable def LinearSys.reach (sys : LinearSys 𝕋 n) (tFinal Δt : ℝ) (η : ℕ) (X₀ : S n) :
    SetUnion (S n) :=
  ⟨(List.range ⌈tFinal / Δt⌉₊).map (sys.reachStepk Δt η X₀)⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
