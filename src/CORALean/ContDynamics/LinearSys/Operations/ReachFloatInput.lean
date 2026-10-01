import CORALean.ContDynamics.LinearSys.Definitions.ReachOptions
import CORALean.ContDynamics.LinearSys.Operations.InputSolutionFloat
import CORALean.ContDynamics.LinearSys.Operations.ReachFloatInputStep
import CORALean.ContDynamics.LinearSys.Operations.ReachOrderFloat
import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalStepFloat
import CORALean.ContDynamics.Reach.Definitions.InputParams
import CORALean.ContDynamics.Reach.Operations.Steps
import CORALean.ContSet.Conversion.Float.Interval_to_Zonotope
import CORALean.Global.Float.ToRat

/-!
# Recursive reachability with inputs in floats: CORA's `priv_reach_standard`

`ẋ = Ax + Bu`, `u(t) ∈ U` arbitrary in time, computed in `𝕋`: `X₀`, `U` (in
input space), `Δt`, `η`, `ρ` and `N` read as `reachFloat` reads them. `V = B U`
is split at its stored centre into the constant `ũ` and `Ũ = V - ũ ∋ 0`, as
CORA's `canonicalForm` splits it, so `0 ∈ U` is not asked.

The constant contributes `P̃(Δt)` per step, and `P̃^R(τ_0)` within the first
window: the input set `[0, ũ]` over one step, which holds `∫₀^τ e^{Aσ}dσ ũ` at
every `τ ≤ Δt` (`inputReach_mono`). `Ũ` contributes `P^R(Δt)` per step, and
the loop (`reachFloatInputStep`) runs CORA's: `H ← reduce([e^{AΔt}] H ⊕ P̃(Δt))`
for the time-point and time-interval sets, and `P^R` accumulates the propagated
one-step set. Window `k` is `H(τ_k) ⊕ P^R(t_{k+1})`, time point `k + 1` is
`H(t_{k+1}) ⊕ P^R(t_{k+1})`. Every input set is `inputSolutionFloat`.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The windows `R(τ_0), …, R(τ_{N-1})` and the time-point sets `R_0, …, R_N`
of `ẋ = Ax + Bu` from `X₀` under inputs in `U`, reducing to order `ρ`. -/
def LinearSys.reachFloatInput (sys : LinearSys 𝕋 n) (B : Mat 𝕋 n m)
    (params : Reach.InputParams (Zonotope 𝕋 n) (Zonotope 𝕋 m) ℚ)
    (options : LinearSys.ReachOptions 𝕋) :
    Option (List (Zonotope 𝕋 n) × List (Zonotope 𝕋 n)) := do
  let X₀ := params.R0                                               -- the paper's symbols
  let Δt := options.timeStep
  let η := options.taylorTerms
  let ρ := options.zonotopeOrder
  let N ← Reach.steps params.tStart params.tFinal (ToRat.toRat Δt) -- (tFinal - tStart) / Δt ∈ ℕ
  let η' ← sys.reachOrderFloat Δt Δt η                              -- η, raised until admissible
  let V := Mtimes.mtimes (𝕄 := Mat 𝕋) B params.U                   -- B U, in the state space
  let ũ := (Interval.point V.c).zonotope                            -- {ũ}, V's stored centre
  let Ũ := Recentre.recentre V                                      -- Ũ = V - ũ, holding 0
  let eAΔt := sys.expIntervalFloat Δt Δt η'                         -- [e^{AΔt}], once
  let F := MatExp.intervalCorrectionMatrix (Interval.point sys.A) Δt η'   -- [F], once
  let eA := Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n)) eAΔt    -- [e^{AΔt}] ·
  let Pu := sys.inputSolutionFloat Δt η' ũ                          -- P̃(Δt)
  let seg := LinComb.linComb (Interval.point fun _ => zero).zonotope ũ    -- [0, ũ]
  let PuR := sys.inputSolutionFloat Δt η' seg                       -- P̃^R(τ_0)
  let PU := sys.inputSolutionFloat Δt η' Ũ                          -- P^R(Δt)
  let Htp₁ := Reduce.reduce (eA X₀ ⊞ Pu) ρ                          -- H(t_1)
  let Hti₀ := (LinComb.linComb X₀ (eA X₀) ⊞                         -- H(τ_0) = H^R ⊕ P̃^R
    Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n)) F X₀) ⊞ PuR
  let S := List.iterate (LinearSys.reachFloatInputStep eAΔt Pu ρ)   -- the loop, k = 0 … N-1
    (Htp₁, Hti₀, PU, PU) N
  let Rti := S.map fun s => s.2.1 ⊞ s.2.2.1                         -- H(τ_k) ⊕ P^R(t_{k+1})
  let Rtp := X₀ :: S.map fun s => s.1 ⊞ s.2.2.1                     -- H(t_{k+1}) ⊕ P^R(t_{k+1})
  pure (Rti, Rtp)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
