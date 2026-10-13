import CORALean.ContDynamics.LinearSys.Theorems.ReachOrderFloatSpec
import CORALean.ContDynamics.NeurNetContrSys.Operations.ReachUnionFloat
import CORALean.ContDynamics.NeurNetContrSys.Theorems.ReachFloatOuter

/-!
# `reachUnionFloat` holds every zero-order-hold run at every period boundary

`reachFloat_outer` at the order `reachOrderFloat` finds, for each period boundary
`i ≤ tFinal - tStart` in the list.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic
open Matrix ContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every zero-order-hold run of `H` control periods is, at the `i`-th period boundary, in
the `i`-th set of `reachUnionFloat`. -/
theorem NeurNetContrSys.reachUnionFloat_outer
    (sys : NeurNetContrSys 𝕋 (fun k => Zonotope (Vec 𝕋 k)) n)
    {params : Reach.Params (Zonotope (Vec 𝕋 n)) ℕ} {options : NeurNetContrSys.ReachOptions 𝕋}
    {Rs : List (Zonotope (Vec 𝕋 n))} (h : sys.reachUnionFloat params options = some Rs)
    (hΔt : 0 < toReal options.Δt) {π : Vec ℝ n → Vec ℝ n} (hπ : sys.contr.Sound π)
    {x : ℝ → Vec ℝ n}
    (traj : sys.Trajectory π ((options.N : ℝ) * toReal options.Δt)
      (params.tFinal - params.tStart) params.X₀ x) :
    Rs.length = params.tFinal - params.tStart + 1 ∧ ∀ (i : ℕ) (hi : i < Rs.length),
      x ((i : ℝ) * ((options.N : ℝ) * toReal options.Δt))
        ∈ construct Rs[i] := by -- --- PROOF ---
  obtain ⟨R₀, tStart, tFinal⟩ := params
  obtain ⟨Δt, N, η, o, ho⟩ := options
  dsimp only at h hΔt traj ⊢
  simp only [NeurNetContrSys.reachUnionFloat, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at h
  obtain ⟨η', hη', rfl⟩ := h
  have hadm := (LinearSys.reachOrderFloat_spec hη').1
  refine ⟨by simp, fun i hi => ?_⟩
  have hiH : i ≤ tFinal - tStart := by simp at hi; omega
  simpa using sys.reachFloat_outer o η' N ho hΔt hadm hπ traj i hiH

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
