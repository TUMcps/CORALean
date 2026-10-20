module

public import CORALean.Specification.STL.Definitions.ReachSequence

@[expose] public section

/-!
# A c-divisible reach sequence is constant between sample times

[1, Lemma 2]'s proof uses that `R` "changes values only at points divisible by c": `R` is
constant on every open block `(jc, jc + c)`, because no breakpoint of `T ⊆ ℕc` falls strictly
inside one.

## Inputs
* `c` – block length
* `T` – finite set of change times
* `R` – reach sequence
* `j` – block index
* `s` – first time
* `t` – second time

## Hypotheses
* `hT` – the reach sequence changes only at those times
* `hdiv` – the times are divisible by the block length
* `hs` – the first time lies strictly inside the block
* `ht` – the second time lies strictly inside the block

## Conclusion
* the reach sets at both times are equal

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". ATVA, LNCS 9938, pp. 412-427, 2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {X : Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ReachSequence.eq_of_cDivisible {c : ℝ≥0} {T : Finset ℝ≥0} {R : ℝ≥0 → Set X}
    (hT : ReachSequence.FinRep T R) (hdiv : ReachSequence.CDivisible c T) (j : ℕ) {s t : ℝ≥0}
    (hs : j * c < s ∧ s < j * c + c) (ht : j * c < t ∧ t < j * c + c) :
    R s = R t := by -- --- PROOF ---
  refine hT s t fun u hu hmem => ?_
  obtain ⟨m, rfl⟩ := hdiv u hu
  -- a multiple `m c` between two points of the block lies strictly between `j c` and `(j + 1) c`
  have hlo : j * c < m * c ∧ m * c < j * c + c := by
    rcases Set.mem_uIcc.1 hmem with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact ⟨hs.1.trans_le h₁, h₂.trans_lt ht.2⟩
    · exact ⟨ht.1.trans_le h₁, h₂.trans_lt hs.2⟩
  have hc : 0 < c := by
    by_contra h0
    obtain rfl : c = 0 := by simpa using h0
    simp at hs
  have h₁ : j < m := by exact_mod_cast lt_of_mul_lt_mul_right hlo.1 hc.le
  have h₂ : m < j + 1 := by
    have : m * c < ((j + 1 : ℕ) : ℝ≥0) * c := by push_cast; rw [add_mul, one_mul]; exact hlo.2
    exact_mod_cast lt_of_mul_lt_mul_right this hc.le
  omega

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
