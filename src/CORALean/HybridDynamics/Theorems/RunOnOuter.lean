import CORALean.HybridDynamics.Theorems.TrajectoryMemIccRight
import CORALean.HybridDynamics.Definitions.InvariantOn

/-!
# A run never leaves the invariant, up to its own jump count

`RunOnOuter`'s statement of `RunOuter`: the invariant read at index `k` bounds
the state after `m` further jumps by index `k + m`, so a location visited twice
on the way there answers to whichever index the run has reached each time.

Induction on the run generalising `k`, since the recursive call reads the
invariant at `k + 1`. The `jump` case then owes an index rearrangement,
`k + (k' + 1) = (k + 1) + k'`, which `omega` settles once it is named.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {L 𝕋 : Type} [Scalar 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HybridAutomaton.RunOn.mem_of_invariantOn {HA : HybridAutomaton S G L 𝕋 n}
    {R : ℕ → L → S n} (hinv : HA.InvariantOn R) {m k : ℕ} {ℓ ℓ' : L} {x y : Vec ℝ n}
    (run : HA.RunOn m ℓ x ℓ' y) :
    x ∈ construct (R k ℓ) → y ∈ construct (R (k + m) ℓ') := by -- --- PROOF ---
  induction run generalizing k with
  | flow h => exact fun hx => hinv.flow h hx h.mem_Icc_right
  | @jump k' _ _ _ _ _ _ _ h hmem hguard _ ih =>
    intro hx
    have hk : k + (k' + 1) = (k + 1) + k' := by omega
    rw [hk]
    exact ih (hinv.jump hmem (hinv.flow h hx h.mem_Icc_right) hguard)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
