module

public import CORALean.HybridDynamics.Theorems.LocationReachFloatOuterWindow

@[expose] public section

/-!
# `Location.reachFloat` holds every stay of length up to `tFinal`

`LinearSys.reachFloatInput_outer`, read at a stay rather than at a run over the
whole horizon: the windows' enclosures are statements about states, not about
trajectories, so a stay of length `τ ≤ tFinal` is held at each of its times
`t` by the window `k` with `t ∈ [k Δt, (k + 1) Δt]`. The location's combined inputs
`B u + c + E w` lie in `ℓ.inputSetFloat` (`inputSetFloat_outer`), and so in the identity's image
of it.

## Inputs
* `ℓ` – location
* `τ` – stay duration
* `x` – trajectory of the stay
* `u` – input trajectory
* `w` – disturbance trajectory
* `tFinal` – final time
* `options` – reach options
* `X₀` – initial zonotope
* `t` – time within the stay

## Hypotheses
* `traj` – the curves are a stay of the location
* `h₀` – initial state lies in the initial set
* `hτ` – stay duration within the final time
* `ht` – time within the stay

## Conclusion
* some reach set holds the state at the time
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   12-November-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic NormedSpace Matrix ContSet ContSetLike

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {L 𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]
variable {G : ℕ → Type} [∀ n, ContSetLike (G n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every state a stay of length `τ ≤ tFinal` from `X₀` passes through lies in
one of the computed time-interval sets. -/
theorem Location.IsTrajectory.reachFloat_outer {ℓ : Location 𝒵[𝕋] G L 𝕋 n} {τ : ℝ} {x : ℝ → Vec ℝ n}
    {u w} (traj : ℓ.IsTrajectory τ x u w) {tFinal : ℚ} {options : LinearSys.ReachFloatOptions 𝕋}
    {X₀ : Zonotope (Vec 𝕋 n)} (h₀ : x 0 ∈ toSet X₀) (hτ : τ ≤ tFinal) {t : ℝ}
    (ht : t ∈ Set.Icc 0 τ) : -- --- CONCL ---
    ∀ Rs ∈ ℓ.reachFloat tFinal options X₀,
      ∃ R ∈ Rs, x t ∈ toSet R := by -- --- PROOF ---
  intro Rs hRs
  obtain ⟨-, k, hk, hx, -⟩ := traj.reachFloat_outer_window h₀ hτ ht Rs hRs
  exact ⟨_, List.getElem_mem hk, hx⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
