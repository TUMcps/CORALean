module

public import CORALean.ContDynamics.LinearSys.Theorems.ReachOrderFloatSpec
public import CORALean.ContDynamics.NeurNetContrSys.Operations.ReachUnionFloat
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.ReachFloatOuter

@[expose] public section

/-!
# `reachUnionFloat` holds every zero-order-hold run at every period boundary

`reachFloat_outer` at the order `reachOrderFloat` finds, for each period boundary
`i ≤ tFinal - tStart` in the list.

## Inputs
* `sys` – closed-loop system
* `U_ext` – external input zonotope
* `params` – reachability parameters
* `options` – reachability options
* `π` – controller function
* `W` – disturbance set
* `x` – plant states
* `v` – external input signal
* `w` – disturbance signal

## Hypotheses
* `hΔt` – step positive
* `hdt` – the period is `N` steps
* `hπ` – the network encloses `π`
* `hW` – disturbances sent to zero by the disturbance matrix
* `traj` – closed-loop trajectory

## Conclusion
* every run lies in the list's set at its period boundary
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic
open Matrix ContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every zero-order-hold run of `H` control periods is, at the `i`-th period boundary, in
the `i`-th set of `reachUnionFloat`. -/
theorem NeurNetContrSys.reachUnionFloat_outer (sys : NeurNetContrSys (LinearSys 𝕋 n) 𝒵[𝕋] n)
    (U_ext : Zonotope (Vec 𝕋 sys.nExt)) {params : Reach.Params (Zonotope (Vec 𝕋 n)) ℕ}
    {options : NeurNetContrSys.ReachOptions 𝕋} (hΔt : 0 < toReal options.Δt)
    (hdt : sys.dt = (options.N : ℝ) * toReal options.Δt) {π : Vec ℝ n → Vec ℝ sys.m}
    (hπ : sys.contr.Encloses π) {W : Set (Vec ℝ sys.plant.r)}
    (hW : ∀ v ∈ W, Scalar.toRealMat sys.plant.E *ᵥ v = 0) {x : ℝ → Vec ℝ n} {v : ℝ → Vec ℝ sys.nExt}
    {w : ℝ → Vec ℝ sys.plant.r} (traj : sys.IsTrajectory π (params.tFinal - params.tStart) params.X₀
    (construct U_ext) W x v w) : -- --- CONCL ---
    ∀ Rs ∈ sys.reachUnionFloat U_ext params options,
      Rs.length = params.tFinal - params.tStart + 1 ∧ ∀ (i : ℕ) (hi : i < Rs.length),
        x ((i : ℝ) * sys.dt)
          ∈ construct Rs[i] := by -- --- PROOF ---
  intro Rs (h : sys.reachUnionFloat U_ext params options = some Rs)
  obtain ⟨R₀, tStart, tFinal⟩ := params
  obtain ⟨Δt, N, η, o, ho⟩ := options
  dsimp only at h hΔt hdt traj ⊢
  simp only [NeurNetContrSys.reachUnionFloat, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at h
  obtain ⟨η', hη', rfl⟩ := h
  have hadm := (LinearSys.reachOrderFloat_spec _ hη').1
  refine ⟨by simp, fun i hi => ?_⟩
  have hiH : i ≤ tFinal - tStart := by simp at hi; omega
  simpa using sys.reachFloat_outer U_ext o η' N ho hΔt hdt hadm hπ hW traj i hiH

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
