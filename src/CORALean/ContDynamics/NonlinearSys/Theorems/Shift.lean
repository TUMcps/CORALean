import CORALean.ContDynamics.NonlinearSys.NonlinearSys

/-!
# A trajectory re-anchored at a later time

`Trajectory.init` pins the state at `0` and every guarantee in `LinearSys` is
written from `0`, so a method that takes a second step has to move the clock.
This is the move: `fun t => x (t₀ + t)` is a trajectory on any domain the shift
carries into `T`, with the input shifted alongside it.

The field is time-invariant, so `flow` transports without a change of vector
field — the chain rule contributes the factor `1` and nothing else. That is the
only reason re-anchoring is cheap here, and it is why `NonlinearSys` carrying
time in the state rather than as an argument is not a neutral choice.

`R₀'` is a parameter and its membership a hypothesis: the state reached at `t₀`
is what the previous step enclosed, so the caller already has the set and the
proof, and asking for them is what makes this compose.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open ContSet

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]

/-- Every run on `T` is a run on `T'` re-anchored at `t₀`, given a set holding
the state it starts from. -/
theorem NonlinearSys.Trajectory.shift {sys : NonlinearSys n m} {T T' : Set ℝ}
    {R₀ R₀' : S n} {U : S m} {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m} {t₀ : ℝ}
    (traj : sys.Trajectory T R₀ U x u) (hT : Set.MapsTo (fun t => t₀ + t) T' T)
    (h₀ : x t₀ ∈ construct R₀') :
    sys.Trajectory T' R₀' U (fun t => x (t₀ + t)) (fun t => u (t₀ + t)) where
  init := by simpa using h₀
  input t ht := traj.input _ (hT ht)
  flow t ht := by
    have hg : HasDerivWithinAt (fun s : ℝ => t₀ + s) 1 T' t :=
      ((hasDerivAt_id t).const_add t₀).hasDerivWithinAt
    have h := (traj.flow _ (hT ht)).scomp t hg hT
    simpa [Function.comp_def] using h

end CORALean.Real
