import CORALean.Global.Radstrom

/-!
# Rådström's cancellation law, as an equality

`A + X = B + X` gives `A = B` once both are convex and closed and `X` is nonempty
and bounded: the inclusion law of `Global/Radstrom.lean`, once each way.

The source asks `X` bounded and not nonempty, and the lemma is false without it:
`A + ∅ = B + ∅` holds for every `A` and `B`. Its proof opens on "given any
`x₁ ∈ X`", which is where the hypothesis is used without being stated.

## References

* [1] H. Rådström. "An embedding theorem for spaces of convex sets".
      Proc. Amer. Math. Soc. 3 (1952), pp. 165-169.
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Pointwise

variable {α : Type} [NormedAddCommGroup α] [NormedSpace ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Lemma 2]: a bounded nonempty summand cancels between two convex closed
sets. -/
theorem radstrom_cancel_eq {A B X : Set α} (hX : X.Nonempty) (hXb : Bornology.IsBounded X)
    (hAconv : Convex ℝ A) (hAcl : IsClosed A) (hBconv : Convex ℝ B) (hBcl : IsClosed B)
    (h : A + X = B + X) : A = B :=
  subset_antisymm (radstrom_cancel hX hXb hBconv hBcl h.le)
    (radstrom_cancel hX hXb hAconv hAcl h.ge)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
