module

public import CORALean.NN.Theorems.SuffExplanationExact
public import CORALean.NN.Theorems.SuffExplanation

@[expose] public section

/-!
# From separation on the exact image to the pointwise definition

`IsSuffExplanationExact` is [1, Def. 1] stated as a specification on a set; this
reads it back as the inequality the definition is written with. The one gap is
the input side: the predicate ranges over
`construct (ofInterval (explainBox …))`, which `ofInterval_outer` says contains
`construct (explainBox …)`, so the specification form is the stronger of the two
and this direction is the only one that holds for every `S`.

## References

* [1] S. Bassan, Y. Y. Elboher, T. Ladner, M. Althoff and G. Katz. "Explaining
      Fast and Slow: Abstraction and Refinement of Provable Explanations".
      ICML 2025.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Real.OfInterval

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [Real.OfInterval S] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Separation on the exact image is sufficiency in the pointwise sense:
every point of `explainBox` keeps `l` strictly ahead. -/
theorem suffExplanation_of_exact (f : Vec ℝ n → Vec ℝ m) (x : Vec ℝ n) (ε : ℝ)
    (E : Finset (Fin n)) (l : Fin m) (hexact : IsSuffExplanationExact S f x ε E l) :
    IsSuffExplanation f x ε E l := by -- --- PROOF ---
  intro x' hx' j hj
  have hmem : f x' ∈ f '' construct (ofInterval (explainBox x ε E) : S n) :=
    ⟨x', ofInterval_outer _ hx', rfl⟩
  have hd := Set.disjoint_left.mp hexact hmem
  by_contra hc
  exact hd ⟨j, hj, not_lt.mp hc⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
