module

public import CORALean.Specification.Operations.VerifyHalfspace

@[expose] public section

/-!
# `[1, Alg. 2]` answers `unsafe` only from a round whose lower bound crossed

`verifyHalfspace` returns `violated` because some round `r' ≥ r` — the one the
recursion stopped at — has a step `k` and a direction `i` whose lower bound
already exceeds the offset: line 9's test, fired. Both the refutation of the
safe set and the counterexample run are read off that round.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated
      Verification of Linear Systems Using Reachability Analysis with Support
      Functions". HSCC, 2023, Article 5.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       16-September-2026
-- Last update:   11-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {ι : Type}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `[1, Alg. 2]`: `verifyHalfspace` only ever returns `unsafe` because some round already finds
a step and direction whose lower bound crosses the offset. -/
theorem exists_round_of_verifyHalfspace_eq_violated
    {bndUp bndLo : (r : ℕ) → Fin (2 ^ r) → ι → ℝ} {d : ι → ℝ} :
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
      · obtain ⟨r', hr', hb⟩ := exists_round_of_verifyHalfspace_eq_violated h
        exact ⟨r', le_trans (Nat.le_succ r) hr', hb⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
