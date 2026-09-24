import CORALean.HybridDynamics.Theorems.HoldsOfRun
import CORALean.Specification.Theorems.CheckSound

/-!
# A passed check on the invariant holds along every run

`holds_of_invariant` with its hypothesis discharged by running `Specification.check` on
the invariant at the location the run ends in: a `true`, found by evaluation, is the
specification on the state it ends at, with nothing left to prove by hand.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {L 𝕋 : Type} [Scalar 𝕋] {n : ℕ}
variable {ContSet : Type} [CORALean.ContSet ContSet (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem HybridAutomaton.holds_of_check [Contains ContSet (S n)] [IsDisjoint ContSet (S n)]
    {HA : HybridAutomaton S G L 𝕋 n} {R : L → S n} (hinv : HA.Invariant R)
    (spec : Specification ContSet) {ℓ ℓ' : L} {x y : Vec ℝ n} (run : HA.Run ℓ x ℓ' y)
    (hx : x ∈ construct (R ℓ)) :
    (spec.check (R ℓ') = true) → (spec.Holds {y}) :=
  fun h => HybridAutomaton.holds_of_invariant hinv spec run hx (spec.check_sound _ h)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
