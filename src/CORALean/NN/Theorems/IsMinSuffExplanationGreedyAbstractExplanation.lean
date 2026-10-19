module

public import CORALean.NN.Operations.GreedyAbstractExplanation
public import CORALean.NN.Theorems.ExplanationRefineLoopIff
public import CORALean.NN.Theorems.IsMinSuffExplanationGreedyMinimalExplanation

@[expose] public section

/-!
# [1, Prop. 5]: the abstraction-refinement search, and where it lands

[1, Alg. 2] returns a minimal sufficient explanation for the original `f`: its oracle decides
the exact query (`explanationRefineLoop_iff`), so [1, Alg. 1]'s guarantee applies.

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

/-- [1, Prop. 5] (Greedy Minimal Sufficient Explanation Search): [1, Alg. 2]
returns a minimal sufficient explanation for the original `f`. -/
theorem isMinSuffExplanation_greedyAbstractExplanation
    {f : Vec ℝ n → Vec ℝ m} {x : Vec ℝ n} {ε : ℝ} (hε : 0 ≤ ε) {l : Fin m}
    {absSuff genuine : ℕ → Finset (Fin n) → Bool} {N : ℕ}
    (habs : ∀ k E, absSuff k E = true → IsSuffExplanation f x ε E l)
    (hgen : ∀ k E, genuine k E = true → ¬ IsSuffExplanation f x ε E l)
    (hlast : ∀ E, IsSuffExplanation f x ε E l → absSuff N E = true)
    (hl : IsSuffExplanation f x ε Finset.univ l) : -- --- CONCL ---
    IsMinSuffExplanation f x ε (greedyAbstractExplanation n absSuff genuine N) l :=
  isMinSuffExplanation_greedyMinimalExplanation hε
    (explanationRefineLoop_iff habs hgen hlast N 0 (Nat.zero_add N)) hl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
