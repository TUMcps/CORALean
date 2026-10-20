module

public import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.OutputOuter
public import CORALean.Specification.Theorems.HoldsOfOuter

@[expose] public section

/-!
# A specification checked on the output set holds along every run

`LinearSysDT.holds_of_output`'s statement, at the enclosed input sets
`output_outer` reads the output at: `holds_of_reach` for the output rather
than the state, and for the same reason there — `C` in general not invertible.

## Inputs
* `sys` – closed-loop system
* `U_ext` – external input set
* `Y` – output set type
* `o` – maximum zonotope order
* `R₀` – initial set
* `spec` – specification
* `π` – controller function
* `W` – disturbance set
* `x` – states
* `v` – external input signal
* `w` – disturbance signal
* `k` – step

## Hypotheses
* `ho` – order positive
* `hπ` – the network encloses `π`
* `hW` – disturbances sent to zero by the disturbance matrix
* `traj` – closed-loop trajectory
* `h` – specification holds on the output set

## Conclusion
* the specification holds at the output of step `k`
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       07-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Plus Reduce Mtimes

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]
    [OfScalarPoint 𝕋 S]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NeurNetContrSysDT.holds_of_output (sys : NeurNetContrSysDT (LinearSysDT 𝕋 n) S n)
    (U_ext : S sys.nExt) {Y : Type} [CORALean.ContSet Y (Vec ℝ sys.plant.q)]
    {o : ℕ} (ho : 0 < o) (R₀ : S n) (spec : Specification Y)
    {π : Vec ℝ n → Vec ℝ sys.m} (hπ : sys.contr.Encloses π)
    {W : Set (Vec ℝ sys.plant.r)}
    (hW : ∀ v ∈ W, toRealMat sys.plant.E *ᵥ v = 0) {x : ℕ → Vec ℝ n} {v : ℕ → Vec ℝ sys.nExt}
    {w : ℕ → Vec ℝ sys.plant.r} (traj : sys.IsTrajectory π R₀ (construct U_ext) W x v w) (k : ℕ)
    (h : spec.Holds (construct (sys.outputSet U_ext (sys.reach U_ext ⟨R₀, 0, k⟩ ⟨o, ho⟩))))
    :
    spec.Holds {sys.plant.outputEq.eval (x k) (sys.input (π (x k)) (v k))} :=
  spec.holds_of_outer
    (Set.singleton_subset_iff.mpr (sys.output_outer U_ext ho R₀ hπ hW traj k)) h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
