import CORALean.HybridDynamics.Theorems.TrajectoryMemIccRight
import CORALean.HybridDynamics.Definitions.Invariant

/-!
# A run never leaves the invariant

The chaining, and it is the run's own recursion principle: one case per
constructor, each discharging an obligation the invariant already carries. That
is what choosing an inductive family for the run bought — the same shape as
`NeuralNetwork.Sound.enclose_outer`, and for the same reason.

The `jump` case applies `flow` first, at the right endpoint of the stay: the
state a guard is tested against is the one the stay ends at, which is why
`Location.Trajectory.nonneg` has to be a field rather than an afterthought.

Only soundness is chained. Nothing here says the invariant is tight, and a run
that visits a location twice is answered by the same set both times — which is
the price of an inductive invariant and the reason a bounded analysis indexes by
step count instead.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {L 𝕋 : Type} [Scalar 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HybridAutomaton.Run.mem_of_invariant {HA : HybridAutomaton S G L 𝕋 n}
    {R : L → S n} (hinv : HA.Invariant R) {ℓ ℓ' : L} {x y : Vec ℝ n}
    (run : HA.Run ℓ x ℓ' y) : x ∈ construct (R ℓ) → y ∈ construct (R ℓ') := by
  induction run with
  | flow h => exact fun hx => hinv.flow h hx h.mem_Icc_right
  | jump h hmem hguard _ ih =>
    exact fun hx => ih (hinv.jump hmem (hinv.flow h hx h.mem_Icc_right) hguard)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
