module

public import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.ReachOuter
public import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.SimulateIsTrajectory

@[expose] public section

/-!
# A sampled run stays inside the reachable set

`simulate_isTrajectory` handed to `reach_outer`: the one fact `simulate` is for,
stated once so nothing downstream redoes the induction on `reach`.

## Inputs
* `sys` – closed-loop system
* `o` – maximum zonotope order
* `U_ext` – external input set
* `R₀` – initial set
* `π` – controller function
* `v` – external input signal
* `x₀` – initial state
* `k` – step

## Hypotheses
* `ho` – order positive
* `hπ` – the network encloses `π`
* `hv` – external inputs lie in `U_ext`
* `hx₀` – start lies in `R₀`

## Conclusion
* the simulated state lies in the reachable set
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       06-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Plus Reduce Mtimes

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]
variable [OfScalarPoint 𝕋 S]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NeurNetContrSysDT.simulate_mem_reach (sys : NeurNetContrSysDT (LinearSysDT 𝕋 n) S n) {o : ℕ}
    (U_ext : S sys.nExt) (ho : 0 < o)
    (R₀ : S n) {π : Vec ℝ n → Vec ℝ sys.m} (hπ : sys.contr.Encloses π)
    {v : ℕ → Vec ℝ sys.nExt} (hv : ∀ k, v k ∈ construct U_ext)
    {x₀ : Vec ℝ n} (hx₀ : x₀ ∈ construct R₀) (k : ℕ) : -- --- CONCL ---
    sys.simulate π v x₀ k ∈ construct (sys.reach U_ext ⟨R₀, 0, k⟩ ⟨o, ho⟩) :=
  sys.reach_outer U_ext ho R₀ hπ
    (fun v hv => by rw [Set.mem_singleton_iff.1 hv, Matrix.mulVec_zero])
    (sys.simulate_isTrajectory π (Set.mem_singleton 0) hv hx₀) k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
