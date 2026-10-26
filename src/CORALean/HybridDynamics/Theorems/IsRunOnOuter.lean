module

public import CORALean.HybridDynamics.Theorems.IsTrajectoryMemIccRight
public import CORALean.HybridDynamics.Definitions.IsInvariantOn

@[expose] public section

/-!
# A run never leaves the invariant, up to its own jump count

`RunOnOuter`'s statement of `RunOuter`: the invariant read at index `k` bounds
the state after `m` further jumps by index `k + m`, so a location visited twice
on the way there answers to whichever index the run has reached each time.

Induction on the run generalising `k`, since the recursive call reads the
invariant at `k + 1`. The `jump` case then owes an index rearrangement,
`k + (k' + 1) = (k + 1) + k'`, which `omega` settles once it is named.

## Inputs
* `HA` – hybrid automaton
* `R` – reach set
* `m` – number of jumps
* `k` – start index
* `ℓ` – location
* `ℓ'` – end location
* `x` – trajectory of the stay
* `y` – end state

## Hypotheses
* `hinv` – the sets are an indexed invariant
* `run` – run of `m` jumps from `x` to `y`

## Conclusion
* membership at the start index implies membership at the end index
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       06-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {L 𝕋 : Type} [Scalar 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HybridAutomaton.IsRunOn.mem_of_isInvariantOn {HA : HybridAutomaton S G L 𝕋 n}
    {R : ℕ → L → S n} (hinv : HA.IsInvariantOn R) {m k : ℕ} {ℓ ℓ' : L} {x y : Vec ℝ n}
    (run : HA.IsRunOn m ℓ x ℓ' y) : -- --- CONCL ---
    x ∈ construct (R k ℓ) → y ∈ construct (R (k + m) ℓ') := by -- --- PROOF ---
  induction run generalizing k with
  | flow h => exact fun hx => hinv.flow h hx h.mem_Icc_right
  | @jump k' _ _ _ _ _ _ _ _ h hmem hguard _ ih =>
    intro hx
    have hk : k + (k' + 1) = (k + 1) + k' := by omega
    rw [hk]
    exact ih (hinv.jump hmem (hinv.flow h hx h.mem_Icc_right) hguard)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
