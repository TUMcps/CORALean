module

public import CORALean.Specification.Operations.VerifyHalfspace
public import CORALean.Specification.Theorems.Containment
public import CORALean.Specification.Theorems.HoldsIUnion

@[expose] public section

/-!
# `[1, Alg. 2]`: `safe` proves the whole horizon never leaves the safe halfspaces

`verifyHalfspace` settles `safe` at some round `r'`: every step's bound there already clears
its offset, so `holds_safeSet_of_bounds` closes each step and `holds_iUnion` merges them —
whatever `r'`'s steps cover, `hcover` says, already subsumes `R`, with no fixed
discretization assumed, only that *some* round's does.

## Inputs
* `ℓ` – directions
* `d` – offsets
* `S` – covering sets per round
* `R` – reachable set
* `bndLo` – lower bounds per round and step
* `u` – support bounds of the covering sets
* `r` – first round
* `fuel` – number of rounds

## Hypotheses
* `hcover` – every round's sets cover the reachable set
* `h` – the search answers safe

## Conclusion
* the safe set specification holds of the reachable set

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Reachability Analysis with Support Functions". Proceedings of the 26th ACM
      International Conference on Hybrid Systems: Computation and Control, 2023.
-/

-- Authors:       Claude Opus 5
-- Written:       16-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {α ι : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `verifyHalfspace` only ever returns `safe` because some round already does, on its own —
the round the recursion actually stopped at. -/
theorem aux_exists_safe_round {bndUp bndLo : (r : ℕ) → Fin (2 ^ r) → ι → ℝ}
    {d : ι → ℝ} :
    ∀ {r fuel : ℕ}, verifyHalfspace bndUp bndLo d r fuel = .safe →
      ∃ r' ≥ r, ∀ (k : Fin (2 ^ r')) (i : ι), bndUp r' k i ≤ d i
  | r, 0, h => by
      simp only [verifyHalfspace] at h
      split_ifs at h with h1 h2
      · exact ⟨r, le_refl r, h2⟩
  | r, fuel + 1, h => by
      simp only [verifyHalfspace] at h
      split_ifs at h with h1 h2
      · exact ⟨r, le_refl r, h2⟩
      · obtain ⟨r', hr', hb⟩ := aux_exists_safe_round h
        exact ⟨r', le_trans (Nat.le_succ r) hr', hb⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- `[1, Alg. 2]`: once `verifyHalfspace` settles `safe`, the set every `SupportBound` here
bounds — `R`, covered by some round's steps — never leaves the halfspace polytope `d` cuts
out in the directions `ℓ`. -/
theorem holds_safeSet_of_verifyHalfspace_safe {ℓ : ι → α →ₗ[ℝ] ℝ} {d : ι → ℝ}
    {S : (r : ℕ) → Fin (2 ^ r) → Set α} {R : Set α} {bndLo : (r : ℕ) → Fin (2 ^ r) → ι → ℝ}
    (u : ∀ (r : ℕ) (k : Fin (2 ^ r)) (i : ι), SupportBound (S r k) (ℓ i))
    (hcover : ∀ r : ℕ, R ⊆ ⋃ k, S r k) {r fuel : ℕ}
    (h : verifyHalfspace (fun r k i => (u r k i).val) bndLo d r fuel = .safe) : -- --- CONCL ---
    (Specification.safeSet {x | ∀ i, ℓ i x ≤ d i}).Holds R := by -- --- PROOF ---
  obtain ⟨r', hr', hb⟩ := aux_exists_safe_round h
  refine Set.Subset.trans (hcover r') ?_
  exact Specification.holds_iUnion (Specification.safeSet _)
    fun k => Specification.holds_safeSet_of_bounds ℓ d (u r' k) (hb k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
