import CORALean.NN.Theorems.MinSuffExplanation

/-!
# Minimality is a counterexample per feature

What [1, Alg. 2] accumulates while it runs: for each feature it refuses to free,
a concrete input in the box one feature wider on which some rival catches the
target. That collection *is* minimality — the equivalence below — so the loop
returns a certificate rather than an appeal to how it searched, which is the
same trade `Global.LinProg` makes for a bound.

The counterexample is checked on `nn` itself, never on an abstraction: one found
against a enclosed set may be spurious, and [1, Alg. 2, l. 9] is exactly that
check.

## References

* [1] S. Bassan, Y. Y. Elboher, T. Ladner, M. Althoff and G. Katz. "Explaining
      Fast and Slow: Abstraction and Refinement of Provable Explanations".
      ICML 2025.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `E` is minimal exactly when it is sufficient and every feature of it has a
counterexample witnessing that dropping it is not. -/
theorem minSuffExplanation_iff_counterexample (f : Vec ℝ n → Vec ℝ m)
    (x : Vec ℝ n) (ε : ℝ) (E : Finset (Fin n)) (l : Fin m) :
    IsMinSuffExplanation f x ε E l ↔
      IsSuffExplanation f x ε E l ∧ ∀ i ∈ E,
        ∃ x' ∈ construct (explainBox x ε (E \ {i})),
          ∃ j, j ≠ l ∧ f x' l ≤ f x' j := by -- --- PROOF ---
  constructor
  · rintro ⟨hsuff, hmin⟩
    refine ⟨hsuff, fun i hi => ?_⟩
    -- no counterexample anywhere in the wider box is sufficiency there
    by_contra hnone
    refine hmin i hi (fun x' hx' j hj => ?_)
    by_contra hlt
    exact hnone ⟨x', hx', j, hj, not_lt.mp hlt⟩
  · rintro ⟨hsuff, hce⟩
    refine ⟨hsuff, fun i hi hdrop => ?_⟩
    obtain ⟨x', hx', j, hj, hle⟩ := hce i hi
    exact absurd (hdrop x' hx' j hj) (not_lt.mpr hle)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
