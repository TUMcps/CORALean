module

public import CORALean.NN.Operations.RefineVerifyFrom
public import CORALean.NN.Theorems.EncloseReduceAtOuter

@[expose] public section

/-!
# The refinement loop is sound from any order pattern

[1, Alg. 3]: `VERIFIED` from any order pattern and with any number of iterations left means
every output of the network on the input set misses the unsafe set `Sᵤ`, whatever the
refinement rule — provided the disjointness test is sound, `isDisjoint Y` only when `Y` misses
`Sᵤ`. The returning iteration's enclosure holds every output (`encloseReduceAt_outer`), so it
missing `Sᵤ` is enough.

## Inputs
* `rn` – refinable network
* `ρ` – order after reduction
* `X` – input set
* `Su` – unsafe set
* `isDisjoint` – test that the output set misses the unsafe set
* `refineStep` – refinement of the schedule

## Hypotheses
* `hdis` – a passed test implies the set avoids the unsafe set

## Conclusion
* a verified result means no output on the input set is unsafe

## References

* [1] [T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural Network Verification
      using Sensitivity Analysis". Proceedings of the 26th ACM International Conference on Hybrid
      Systems: Computation and Control,
      2023.](../../../../references/2023/ladner-hscc-abstraction-refinement.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem RefinableNetwork.refineVerifyFrom_sound (rn : RefinableNetwork S n m) (ρ : ℕ)
    {X : S n} {Su : Set (Vec ℝ m)} {isDisjoint : S m → Bool}
    (hdis : ∀ Y, isDisjoint Y = true → ∀ y ∈ construct Y, y ∉ Su)
    (refineStep : Schedule → Schedule) : -- --- CONCL ---
    ∀ (I : ℕ) (ψ : Schedule), rn.refineVerifyFrom ρ X isDisjoint refineStep ψ I = true →
      ∀ x ∈ construct X, rn.eval x ∉ Su := by -- --- PROOF ---
  intro I
  induction I with
  | zero => intro ψ h; simp [RefinableNetwork.refineVerifyFrom] at h
  | succ I ih =>
    intro ψ h x hx
    simp only [RefinableNetwork.refineVerifyFrom] at h
    split at h
    · -- the iteration that returned: its enclosure holds the output and misses `Sᵤ`
      exact hdis _ (by assumption) _ (rn.encloseReduceAt_outer ρ ψ X x hx)
    · exact ih _ h x hx

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
