module

public import CORALean.NN.Definitions.SuffExplanation

@[expose] public section

/-!
# Sufficiency only becomes easier to keep as more features are pinned

Fixing a superset of a sufficient `E` is sufficient too: pinning more
coordinates only shrinks `explainBox`, so the same argument that worked over
the wider box works over the narrower one. This needs `0 ≤ ε`, [1]'s own
typing of a perturbation *radius* — for `ε < 0` a coordinate left free is an
empty range, so a proper subset can be vacuously "sufficient" without the
target actually leading there, and monotonicity fails.

`[1, Alg. 1]`'s minimality argument is the one place this is used: a feature kept
because dropping it broke sufficiency at some larger, earlier candidate set
still cannot be dropped from any smaller set the loop later settles on.

## References

* [1] S. Bassan, Y. Y. Elboher, T. Ladner, M. Althoff and G. Katz. "Explaining
      Fast and Slow: Abstraction and Refinement of Provable Explanations".
      ICML 2025.
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A sufficient explanation stays sufficient at any superset of its features,
over a nonnegative radius. -/
theorem IsSuffExplanation.mono {f : Vec ℝ n → Vec ℝ m} {x : Vec ℝ n} {ε : ℝ} (hε : 0 ≤ ε)
    {E E' : Finset (Fin n)} (hE : E ⊆ E') {l : Fin m} (h : IsSuffExplanation f x ε E l) :
    IsSuffExplanation f x ε E' l := by -- --- PROOF ---
  refine fun x' hx' j hj => h x' (fun i => ?_) j hj
  have hi' : (explainBox x ε E').inf i ≤ x' i ∧ x' i ≤ (explainBox x ε E').sup i := hx' i
  show (explainBox x ε E).inf i ≤ x' i ∧ x' i ≤ (explainBox x ε E).sup i
  by_cases hi : i ∈ E
  · -- `i` is pinned on both sides, so the two boxes agree at `i`
    have hi'' : i ∈ E' := hE hi
    simp only [explainBox, if_pos hi, if_pos hi''] at hi' ⊢
    exact hi'
  · by_cases hiE' : i ∈ E'
    · -- pinned on the narrower side only: the wider box's slack is free
      simp only [explainBox, if_neg hi, if_pos hiE'] at hi' ⊢
      exact ⟨by linarith [hi'.1, hi'.2], by linarith [hi'.1, hi'.2]⟩
    · -- free on both sides: the same `ε`-window
      simp only [explainBox, if_neg hi, if_neg hiE'] at hi' ⊢
      exact hi'

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
