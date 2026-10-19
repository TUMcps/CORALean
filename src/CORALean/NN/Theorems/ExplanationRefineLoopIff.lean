module

public import CORALean.NN.Operations.ExplanationRefineLoop
public import CORALean.NN.Definitions.MinSuffExplanation

@[expose] public section

/-!
# The refinement loop decides the exact query

The loop's two exits are two of the hypotheses: `habs` is [1, Prop. 3],
separation on an enclosure being sufficiency for `f` as
`suffExplanation_of_abstract` proves, and `hgen` is l. 9-11, a counterexample
that still misclassifies at `f`.

`hlast` is what the printed proposition leaves out: l. 19 is `while true`, so
the loop leaves only by l. 7 or l. 13, and neither guarantee survives a
schedule that stops short of the level whose abstraction *is* `f`, where l. 5
answers exactly. [1, Prop. 2] gives a strictly finer refinement, never that
one. The equivalence holds at every level a warm start could enter at.

## References

* [1] S. Bassan, Y. Y. Elboher, T. Ladner, M. Althoff and G. Katz. "Explaining
      Fast and Slow: Abstraction and Refinement of Provable Explanations".
      ICML 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The loop decides the exact query: l. 5 is sound at every level, l. 9-11 is
sound wherever it fires, and the level the schedule ends at is `f` itself,
where l. 5 is complete as well. -/
theorem explanationRefineLoop_iff {f : Vec ℝ n → Vec ℝ m} {x : Vec ℝ n} {ε : ℝ} {l : Fin m}
    {absSuff genuine : ℕ → Finset (Fin n) → Bool} {N : ℕ}
    (habs : ∀ k E, absSuff k E = true → IsSuffExplanation f x ε E l)
    (hgen : ∀ k E, genuine k E = true → ¬ IsSuffExplanation f x ε E l)
    (hlast : ∀ E, IsSuffExplanation f x ε E l → absSuff N E = true) : -- --- CONCL ---
    ∀ (r k : ℕ), k + r = N → ∀ E : Finset (Fin n),
      (explanationRefineLoop absSuff genuine E k r = true
        ↔ IsSuffExplanation f x ε E l) := by -- --- PROOF ---
  intro r
  induction r with
  | zero =>
      -- the schedule is spent: the abstraction is `f`, and l. 5 answers exactly
      intro k hk E
      rw [Nat.add_zero] at hk
      subst hk
      have h0 : explanationRefineLoop absSuff genuine E k 0 = absSuff k E := rfl
      rw [h0]
      exact ⟨habs k E, hlast E⟩
  | succ r ih =>
      intro k hk E
      have hstep : explanationRefineLoop absSuff genuine E k (r + 1)
          = if absSuff k E then true
            else if genuine k E then false
            else explanationRefineLoop absSuff genuine E (k + 1) r := rfl
      rw [hstep]
      by_cases hb : absSuff k E = true
      · -- l. 5 passed at this level, and [1, Prop. 3] reads that back at `f`
        rw [if_pos hb]
        exact ⟨fun _ => habs k E hb, fun _ => rfl⟩
      · rw [if_neg hb]
        by_cases hc : genuine k E = true
        · -- l. 9-11: the counterexample still misclassifies at `f`, so `E` is not sufficient
          rw [if_pos hc]
          exact ⟨fun h => absurd h Bool.false_ne_true, fun h => absurd h (hgen k E hc)⟩
        · -- l. 15 refines the abstraction, and the loop repeats one level up
          rw [if_neg hc]
          exact ih (k + 1) (by omega) E

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
