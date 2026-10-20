module

public import CORALean.ContDynamics.NeurNetContrSys.Theorems.ReachFloatOuter
public import CORALean.Specification.Theorems.CheckSound
public import CORALean.Specification.Theorems.HoldsOfOuter

@[expose] public section

/-!
# A passed check on the float loop's reachable set holds along it

`NeurNetContrSys.holds_of_check` at `reachFloat`: a `true` from `Specification.check` on the
zonotope `reachFloat` computes, found by evaluation, is the specification on the exact state at
the period boundary, since `reachFloat_outer` puts that state in the zonotope.

## Inputs
* `sys` – closed-loop system
* `U_ext` – external input zonotope
* `o` – maximum zonotope order
* `η` – Taylor order
* `N` – steps per period
* `Δt` – step size
* `H` – number of periods
* `R₀` – initial zonotope
* `π` – controller function
* `W` – disturbance set
* `x` – plant states
* `v` – external input signal
* `w` – disturbance signal
* `spec` – specification
* `i` – period index

## Hypotheses
* `ho` – order positive
* `hΔt` – step positive
* `hdt` – the period is `N` steps
* `hη` – order admissible
* `hπ` – the network encloses `π`
* `hW` – disturbances sent to zero by the disturbance matrix
* `traj` – closed-loop trajectory
* `hi` – period index within the horizon

## Conclusion
* a passed check on the float reachable set implies the specification at the period boundary
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic
open Matrix ContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}
variable {ContSet : Type} [CORALean.ContSet ContSet (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NeurNetContrSys.holds_of_checkFloat [Contains ContSet (Zonotope (Vec 𝕋 n))]
    [IsDisjoint ContSet (Zonotope (Vec 𝕋 n))]
    (sys : NeurNetContrSys (LinearSys 𝕋 n) 𝒵[𝕋] n) (U_ext : Zonotope (Vec 𝕋 sys.nExt))
    (o η N : ℕ) (ho : 0 < o) {Δt : 𝕋} (hΔt : 0 < toReal Δt)
    (hdt : sys.dt = (N : ℝ) * toReal Δt)
    (hη : sys.augmentFloat.OrderAdmissibleFloat Δt Δt η) {H : ℕ} {R₀ : Zonotope (Vec 𝕋 n)}
    {π : Vec ℝ n → Vec ℝ sys.m} (hπ : sys.contr.Encloses π)
    {W : Set (Vec ℝ sys.plant.r)} (hW : ∀ v ∈ W, Scalar.toRealMat sys.plant.E *ᵥ v = 0)
    {x : ℝ → Vec ℝ n} {v : ℝ → Vec ℝ sys.nExt} {w : ℝ → Vec ℝ sys.plant.r}
    (traj : sys.IsTrajectory π H R₀ (construct U_ext) W x v w)
    (spec : Specification ContSet) (i : ℕ) (hi : i ≤ H) : -- --- CONCL ---
    spec.check (sys.reachFloat U_ext ⟨R₀, 0, i⟩ ⟨Δt, N, η, o, ho⟩) →
      (spec.Holds {x ((i : ℝ) * sys.dt)}) :=
  fun h => spec.holds_of_outer (Set.singleton_subset_iff.2
    (sys.reachFloat_outer U_ext o η N ho hΔt hdt hη hπ hW traj i hi)) (spec.check_sound _ h)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
