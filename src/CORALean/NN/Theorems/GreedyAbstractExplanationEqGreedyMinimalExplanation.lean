module

public import CORALean.NN.Operations.GreedyAbstractExplanation
public import CORALean.NN.Theorems.ExplanationRefineLoopIff

@[expose] public section

/-!
# [1, Prop. 5]'s second clause: [1, Alg. 2] ends where [1, Alg. 1] ends

The refinement loop answers what a query on `f` would, under the hypotheses
`explanationRefineLoop_iff` needs, so the two folds are one fold.

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

/-- [1, Prop. 5]'s second clause: the loop answers what a query on `f` would,
so [1, Alg. 2] ends where [1, Alg. 1] ends. -/
theorem greedyAbstractExplanation_eq_greedyMinimalExplanation
    {f : Vec ℝ n → Vec ℝ m} {x : Vec ℝ n} {ε : ℝ} {l : Fin m}
    {absSuff genuine : ℕ → Finset (Fin n) → Bool} {N : ℕ}
    (habs : ∀ k E, absSuff k E = true → IsSuffExplanation f x ε E l)
    (hgen : ∀ k E, genuine k E = true → ¬ IsSuffExplanation f x ε E l)
    (hlast : ∀ E, IsSuffExplanation f x ε E l → absSuff N E = true)
    {suff : Finset (Fin n) → Bool}
    (hsuff : ∀ E, suff E = true ↔ IsSuffExplanation f x ε E l) : -- --- STMT ---
    greedyAbstractExplanation n absSuff genuine N
      = greedyMinimalExplanation n suff := by -- --- PROOF ---
  -- the two oracles decide the same query of `f`, so the two folds are one fold
  have h : (fun E => explanationRefineLoop absSuff genuine E 0 N) = suff :=
    funext fun E => Bool.eq_iff_iff.mpr
      ((explanationRefineLoop_iff habs hgen hlast N 0 (Nat.zero_add N) E).trans (hsuff E).symm)
  rw [greedyAbstractExplanation, h]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
