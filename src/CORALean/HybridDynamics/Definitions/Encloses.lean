module

public import CORALean.HybridDynamics.Definitions.ReachQueue
public import CORALean.HybridDynamics.Definitions.IsRunUntil
public import CORALean.ContSet.HPolytope.Float.Instances
public import CORALean.ContSet.Zonotope.Float.Instances

@[expose] public section

/-!
# `HybridAutomaton.Encloses`

A queue entry is covered by branches `out` if every run that starts in its set, at its location, at
a time not before its lower start time, and ends within `δ` of the horizon ends in a time-interval
set of a branch of the end location. `δ` is at least the step of every location: a stay is cut at
whole steps, so the last step before the horizon is not claimed.

## Inputs
* `HA` – hybrid automaton
* `tFinal` – final time
* `δ` – margin to the horizon
* `out` – branches
* `p` – queue entry

## Output
* the statement that the branches cover the runs from the entry
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float ContSetLike

variable {n : ℕ} {L 𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every run of at most `T` from the entry's set at a time `s` not before `tlo`, with `s + T + δ`
within the horizon, ends in a set of a branch at the end location. -/
def HybridAutomaton.Encloses
    (HA : HybridAutomaton 𝒵[𝕋] (fun k => HPolytope 𝕋 (Vec 𝕋 k)) L 𝕋 n) (tFinal : ℚ) (δ : ℝ)
    (out : List (HybridBranch L 𝕋 n)) (p : HybridPending L 𝕋 n) : Prop :=
  ∀ {T : ℝ} {k : ℕ} {ℓ' : L} {x y : Vec ℝ n}, HA.IsRunUntil T k p.loc x ℓ' y →
    x ∈ toSet p.set → ∀ s : ℝ, (p.tlo : ℝ) ≤ s → s + T + δ ≤ tFinal →
      ∃ b ∈ out, b.loc = ℓ' ∧ ∃ R ∈ b.sets, y ∈ toSet R

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
