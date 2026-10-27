module

public import CORALean.Specification.Theorems.ExistsRoundOfVerifyHalfspaceEqViolated
public import CORALean.Specification.Specification
public import CORALean.Global.SupportFunction.SupportFunction

@[expose] public section

/-!
# `[1, Alg. 2]`: `unsafe` refutes the safe-set specification

`verifyHalfspace` settles `unsafe` at some round `r'`, step `k`, direction `i` with an actual
lower bound past the offset: `SupportWitness.mem` hands back a point of `S r' k` — hence of
`R`, by `hsub` — whose value in direction `i` already exceeds `d i`, outside the halfspace
polytope, so `Specification.aux_not_holds_safeSet_of_mem` refutes `Holds` for `R` outright.

## Inputs
* `ℓ` – directions
* `d` – offsets
* `S` – inner sets per round
* `R` – reachable set
* `bndUp` – upper bounds per round and step
* `w` – support witnesses of the inner sets
* `r` – first round
* `fuel` – number of rounds

## Hypotheses
* `hsub` – every round's sets lie inside the reachable set
* `h` – the search answers unsafe

## Conclusion
* the safe set specification fails for the reachable set

## References

* [1] [M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Reachability Analysis with Support Functions". Proceedings of the 26th ACM
      International Conference on Hybrid Systems: Computation and Control,
      2023.](../../../../references/2023/wetzlinger-hscc-support-functions.md)
-/

-- Authors:       Claude Opus 5
-- Written:       16-September-2026
-- Last update:   11-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {α ι : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
variable {α : Type}

/-- A point of `X` outside `S` refutes the safe-set specification for `X`. -/
private theorem Specification.aux_not_holds_safeSet_of_mem {S X : Set α} {x : α} (hx : x ∈ X)
    (hS : x ∉ S) :
    ¬ (Specification.safeSet S).Holds X :=
  fun h => hS (h hx)

end


-- =======================================  MAIN THEOREM  ======================================= --

/-- `[1, Alg. 2]`: once `verifyHalfspace` settles `unsafe`, `R` — anything some round's steps
sit inside, by `hsub` — cannot satisfy the halfspace specification `d` cuts out in the
directions `ℓ`. -/
theorem not_holds_safeSet_of_verifyHalfspace_violated {ℓ : ι → α →ₗ[ℝ] ℝ} {d : ι → ℝ}
    {S : (r : ℕ) → Fin (2 ^ r) → Set α} {R : Set α} {bndUp : (r : ℕ) → Fin (2 ^ r) → ι → ℝ}
    (w : ∀ (r : ℕ) (k : Fin (2 ^ r)) (i : ι), SupportWitness (S r k) (ℓ i))
    (hsub : ∀ (r : ℕ) (k : Fin (2 ^ r)), S r k ⊆ R) {r fuel : ℕ}
    (h : verifyHalfspace bndUp (fun r k i => (w r k i).val) d r fuel = .violated) : -- --- CONCL ---
    ¬ (Specification.safeSet {x | ∀ i, ℓ i x ≤ d i}).Holds R := by -- --- PROOF ---
  obtain ⟨r', hr', k, i, hlt⟩ := exists_round_of_verifyHalfspace_eq_violated h
  obtain ⟨x, hxS, hxle⟩ := (w r' k i).mem
  refine Specification.aux_not_holds_safeSet_of_mem (hsub r' k hxS) fun hmem => ?_
  exact absurd (hmem i) (not_le.mpr (lt_of_lt_of_le hlt hxle))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
