import CORALean.HybridDynamics.Definitions.Location

/-!
# A stay in a location is a linear trajectory

`Location.Trajectory` and `LinearSys.Trajectory` differ in exactly two fields:
the location's is anchored at a point and additionally confined to the
invariant, the linear one is anchored at a set and knows no invariant. Naming a
set the initial point lies in is therefore all it takes to hand a stay to the
whole of `LinearSys`, and the invariant is simply dropped — it only ever
tightens an enclosure, never justifies one.

The time domain is `Set.Icc 0 τ` on the location's own clock, which is the shape
every bounded statement in `LinearSys` asks for. `Trajectory.restrict` is what
makes the other direction free where it is needed: a stay stated on a longer
domain restricts to this one.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, ContSet (G n) (Vec ℝ n)]
variable {L 𝕋 : Type} [Scalar 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The stay read as a run of the location's own linear system, starting in any
set that holds its initial point. -/
theorem Location.Trajectory.linearSys {ℓ : Location S G L 𝕋 n} {τ : ℝ}
    {x u : ℝ → Vec ℝ n} (traj : ℓ.Trajectory τ x u) {R₀ : S n}
    (h₀ : x 0 ∈ construct R₀) :
    ℓ.dynamics.Trajectory (Set.Icc 0 τ) R₀ ℓ.U x u where
  init := h₀
  input := traj.input
  flow := traj.flow

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
