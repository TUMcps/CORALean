module

public import CORALean.ContDynamics.LinearSysDT.LinearSysDT

@[expose] public section

/-!
# A held run is a trajectory

`IsCanonicalHeldTrajectory`'s single `u` reused at every step is `IsCanonicalTrajectory`'s `u` at
`fun _ => u` — a restriction, not a separate guarantee. So `reach_outer` already
encloses a held run, and what `reachHeld` buys over `reach` is precision, not
soundness: the point of a closed form is losing less, not covering more.

## Inputs
* `sys` – system
* `R₀` – initial set
* `U` – input set
* `x` – trajectory
* `u` – held input

## Hypotheses
* `h` – held trajectory

## Conclusion
* a held run is a trajectory with constant input
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- A held run at `fun _ => u`, so `LinearSysDT.reach_outer` covers it too. -/
theorem LinearSysDT.IsCanonicalHeldTrajectory.toIsTrajectory {sys : LinearSysDT 𝕋 n} {R₀ U : S n}
    {x : ℕ → Vec ℝ n} {u : Vec ℝ n} (h : sys.IsCanonicalHeldTrajectory R₀ U x u) :
    sys.IsCanonicalTrajectory R₀ U x (fun _ => u) where
  init := h.init
  input _ := h.input
  step := h.step

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
