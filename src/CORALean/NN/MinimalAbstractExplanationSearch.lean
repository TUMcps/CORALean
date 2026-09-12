import CORALean.NN.MinimalExplanationSearch

/-!
# [1, Prop. 5]: the abstraction-refinement search, and where it lands

[1, Alg. 2] is [1, Alg. 1] with one substitution: each `suff` call is answered
by the do-while of l. 4-19 instead of by a query on `f`, so
`greedyAbstractExplanation` is `greedyMinimalExplanation` at that composite
oracle and inherits its correctness once the oracle is shown exact.

`aux_refineLoop`'s two exits are two of the hypotheses: `habs` is [1, Prop. 3],
separation on an enclosure being sufficiency for `f` as
`suffExplanation_of_abstract` proves, and `hgen` is l. 9-11, a counterexample
that still misclassifies at `f`. Neither is computed, for [1, Alg. 1]'s reason.

`hlast` is what the printed proposition leaves out: l. 19 is `while true`, so
the loop leaves only by l. 7 or l. 13, and neither guarantee below survives a
schedule that stops short of the level whose abstraction *is* `f`, where l. 5
answers exactly. [1, Prop. 2] gives a strictly finer refinement, never that
one. `aux_refineLoop_iff` holds at every level a warm start could enter at.

## References

* [1] S. Bassan, Y. Y. Elboher, T. Ladner, M. Althoff and G. Katz. "Explaining
      Fast and Slow: Abstraction and Refinement of Provable Explanations".
      ICML 2025.
-/

-- Authors:       Tobias Ladner
-- Written:       12-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- [1, Alg. 2, l. 4-19]: the do-while at candidate set `E`, entered at
abstraction level `k` with `r` refinements still to spend. -/
def aux_refineLoop (absSuff genuine : ℕ → Finset (Fin n) → Bool) (E : Finset (Fin n)) :
    ℕ → ℕ → Bool
  | k, 0 => absSuff k E
  | k, r + 1 =>
      if absSuff k E then true
      else if genuine k E then false
      else aux_refineLoop absSuff genuine E (k + 1) r

/-- The loop decides the exact query: l. 5 is sound at every level, l. 9-11 is
sound wherever it fires, and the level the schedule ends at is `f` itself,
where l. 5 is complete as well. -/
theorem aux_refineLoop_iff {f : Vec ℝ n → Vec ℝ m} {x : Vec ℝ n} {ε : ℝ} {l : Fin m}
    {absSuff genuine : ℕ → Finset (Fin n) → Bool} {N : ℕ}
    (habs : ∀ k E, absSuff k E = true → IsSuffExplanation f x ε E l)
    (hgen : ∀ k E, genuine k E = true → ¬ IsSuffExplanation f x ε E l)
    (hlast : ∀ E, IsSuffExplanation f x ε E l → absSuff N E = true) :
    ∀ (r k : ℕ), k + r = N → ∀ E : Finset (Fin n),
      (aux_refineLoop absSuff genuine E k r = true
        ↔ IsSuffExplanation f x ε E l) := by -- --- PROOF ---
  intro r
  induction r with
  | zero =>
      -- the schedule is spent: the abstraction is `f`, and l. 5 answers exactly
      intro k hk E
      rw [Nat.add_zero] at hk
      subst hk
      have h0 : aux_refineLoop absSuff genuine E k 0 = absSuff k E := rfl
      rw [h0]
      exact ⟨habs k E, hlast E⟩
  | succ r ih =>
      intro k hk E
      have hstep : aux_refineLoop absSuff genuine E k (r + 1)
          = if absSuff k E then true
            else if genuine k E then false
            else aux_refineLoop absSuff genuine E (k + 1) r := rfl
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


/-- [1, Alg. 2]: [1, Alg. 1]'s loop, every `suff` call answered by the refinement
loop entered at the coarsest level with `N` refinements to spend. -/
def greedyAbstractExplanation (n : ℕ) (absSuff genuine : ℕ → Finset (Fin n) → Bool) (N : ℕ) :
    Finset (Fin n) :=
  greedyMinimalExplanation n fun E => aux_refineLoop absSuff genuine E 0 N


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 5] (Greedy Minimal Sufficient Explanation Search): [1, Alg. 2]
returns a minimal sufficient explanation for the original `f`. -/
theorem isMinSuffExplanation_greedyAbstractExplanation
    {f : Vec ℝ n → Vec ℝ m} {x : Vec ℝ n} {ε : ℝ} (hε : 0 ≤ ε) {l : Fin m}
    {absSuff genuine : ℕ → Finset (Fin n) → Bool} {N : ℕ}
    (habs : ∀ k E, absSuff k E = true → IsSuffExplanation f x ε E l)
    (hgen : ∀ k E, genuine k E = true → ¬ IsSuffExplanation f x ε E l)
    (hlast : ∀ E, IsSuffExplanation f x ε E l → absSuff N E = true)
    (hl : IsSuffExplanation f x ε Finset.univ l) :
    IsMinSuffExplanation f x ε (greedyAbstractExplanation n absSuff genuine N) l :=
  isMinSuffExplanation_greedyMinimalExplanation hε
    (aux_refineLoop_iff habs hgen hlast N 0 (Nat.zero_add N)) hl

/-- [1, Prop. 5]'s second clause: the loop answers what a query on `f` would,
so [1, Alg. 2] ends where [1, Alg. 1] ends. -/
theorem greedyAbstractExplanation_eq_greedyMinimalExplanation
    {f : Vec ℝ n → Vec ℝ m} {x : Vec ℝ n} {ε : ℝ} {l : Fin m}
    {absSuff genuine : ℕ → Finset (Fin n) → Bool} {N : ℕ}
    (habs : ∀ k E, absSuff k E = true → IsSuffExplanation f x ε E l)
    (hgen : ∀ k E, genuine k E = true → ¬ IsSuffExplanation f x ε E l)
    (hlast : ∀ E, IsSuffExplanation f x ε E l → absSuff N E = true)
    {suff : Finset (Fin n) → Bool}
    (hsuff : ∀ E, suff E = true ↔ IsSuffExplanation f x ε E l) :
    greedyAbstractExplanation n absSuff genuine N
      = greedyMinimalExplanation n suff := by -- --- PROOF ---
  -- the two oracles decide the same query of `f`, so the two folds are one fold
  have h : (fun E => aux_refineLoop absSuff genuine E 0 N) = suff :=
    funext fun E => Bool.eq_iff_iff.mpr
      ((aux_refineLoop_iff habs hgen hlast N 0 (Nat.zero_add N) E).trans (hsuff E).symm)
  rw [greedyAbstractExplanation, h]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
