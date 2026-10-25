module

public import CORALean.HybridDynamics.Theorems.IsTrajectoryMemIccRight
public import CORALean.HybridDynamics.Definitions.IsInvariant

@[expose] public section

/-!
# A run never leaves the invariant

The chaining, and it is the run's own recursion principle: one case per constructor, each
discharging an obligation the invariant already carries; the same shape as
`NeuralNetwork.Encloses.enclose_outer`. The `jump` case applies `flow` first, at the right endpoint
of the stay: the state a guard is tested against is the one the stay ends at, which is why
`Location.IsTrajectory.nonneg` has to be a field. Only soundness is chained: a run that visits a
location twice is answered by the same set both times, the price of an inductive invariant and the
reason a bounded analysis indexes by step count.

## Inputs
* `HA` – hybrid automaton
* `R` – reach set
* `ℓ` – location
* `ℓ'` – end location
* `x` – trajectory of the stay
* `y` – end state

## Hypotheses
* `hinv` – the sets are an invariant
* `run` – run of the automaton from `x` to `y`

## Conclusion
* membership at the start implies membership at the end
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {L 𝕋 : Type} [Scalar 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HybridAutomaton.IsRun.mem_of_invariant {HA : HybridAutomaton S G L 𝕋 n}
    {R : L → S n} (hinv : HA.IsInvariant R) {ℓ ℓ' : L} {x y : Vec ℝ n}
    (run : HA.IsRun ℓ x ℓ' y) : x ∈ construct (R ℓ) → y ∈ construct (R ℓ') := by
  induction run with
  | flow h => exact fun hx => hinv.flow h hx h.mem_Icc_right
  | jump h hmem hguard _ ih =>
    exact fun hx => ih (hinv.jump hmem (hinv.flow h hx h.mem_Icc_right) hguard)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
