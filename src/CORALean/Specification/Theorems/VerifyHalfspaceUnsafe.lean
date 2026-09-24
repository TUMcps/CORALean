import CORALean.Specification.Operations.VerifyHalfspace
import CORALean.Specification.Theorems.Violation
import CORALean.Global.LinProg.LinProg

/-!
# `[1, Alg. 2]`: `unsafe` refutes the safe-set specification

`verifyHalfspace` settles `unsafe` at some round `r'`, step `k`, direction `i` with an actual
lower bound past the offset: `SupportWitness.mem` hands back a point of `S r' k` — hence of
`R`, by `hsub` — whose value in direction `i` already exceeds `d i`, outside the halfspace
polytope, so `Specification.not_holds_safeSet_of_mem` refutes `Holds` for `R` outright.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated
      Verification of Linear Systems Using Reachability Analysis with Support
      Functions". HSCC, 2023, Article 5.
-/

-- Authors:       Tobias Ladner
-- Written:       16-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {α ι : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `verifyHalfspace` only ever returns `unsafe` because some round already finds a step and
direction whose lower bound crosses the offset — the round the recursion actually stopped
at. -/
theorem aux_exists_violated_round {bndUp bndLo : (r : ℕ) → Fin (2 ^ r) → ι → ℝ} {d : ι → ℝ} :
    ∀ {r fuel : ℕ}, verifyHalfspace bndUp bndLo d r fuel = .violated →
      ∃ r' ≥ r, ∃ (k : Fin (2 ^ r')) (i : ι), d i < bndLo r' k i
  | r, 0, h => by
      simp only [verifyHalfspace] at h
      split_ifs at h with h1
      · exact ⟨r, le_refl r, h1⟩
  | r, fuel + 1, h => by
      simp only [verifyHalfspace] at h
      split_ifs at h with h1 h2
      · exact ⟨r, le_refl r, h1⟩
      · obtain ⟨r', hr', hb⟩ := aux_exists_violated_round h
        exact ⟨r', le_trans (Nat.le_succ r) hr', hb⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- `[1, Alg. 2]`: once `verifyHalfspace` settles `unsafe`, `R` — anything some round's steps
sit inside, by `hsub` — cannot satisfy the halfspace specification `d` cuts out in the
directions `ℓ`. -/
theorem not_holds_safeSet_of_verifyHalfspace_violated {ℓ : ι → α →ₗ[ℝ] ℝ} {d : ι → ℝ}
    {S : (r : ℕ) → Fin (2 ^ r) → Set α} {R : Set α} {bndUp : (r : ℕ) → Fin (2 ^ r) → ι → ℝ}
    (w : ∀ (r : ℕ) (k : Fin (2 ^ r)) (i : ι), SupportWitness (S r k) (ℓ i))
    (hsub : ∀ (r : ℕ) (k : Fin (2 ^ r)), S r k ⊆ R) {r fuel : ℕ}
    (h : verifyHalfspace bndUp (fun r k i => (w r k i).val) d r fuel = .violated) :
    ¬ (Specification.safeSet {x | ∀ i, ℓ i x ≤ d i}).Holds R := by
  obtain ⟨r', hr', k, i, hlt⟩ := aux_exists_violated_round h
  obtain ⟨x, hxS, hxle⟩ := (w r' k i).mem
  refine Specification.not_holds_safeSet_of_mem (hsub r' k hxS) fun hmem => ?_
  exact absurd (hmem i) (not_le.mpr (lt_of_lt_of_le hlt hxle))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
