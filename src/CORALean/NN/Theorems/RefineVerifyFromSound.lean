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

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
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
