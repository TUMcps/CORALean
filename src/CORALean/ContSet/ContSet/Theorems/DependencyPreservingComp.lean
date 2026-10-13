import CORALean.ContSet.ContSet.Definitions.DependencyPreserving
import Mathlib.Order.BourbakiWitt

/-!
# [1, Lemma 2]: a composition preserves dependencies

Two steps joined: `B` carries the parameterized set with evaluation function `e`
to the one with `e₁`, `A` carries that to `e₂`, each preserving dependencies, so
`A ∘ B` does. `hA` is the monotonicity [1] states once for all the set operations
it uses — its property (6) — rather than in the lemma, and [1, Lemma 2]'s proof
spends it at exactly the step `hA` is spent at here.

[1, Lemma 1] — that a composition keeps (6) — needs nothing of its own: (6) is
`Monotone` at `Set α` ordered by `⊆`, so Lemma 1 is Mathlib's `Monotone.comp`.
That is why monotonicity is a hypothesis here and never a conclusion.

## References

* [1] N. Kochdumper, B. Schürmann and M. Althoff. "Utilizing Dependencies to
      Obtain Subsets of Reachable Sets". HSCC 2020. arXiv:1910.08354.
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Lemma 2]: dependency preservation composes, the outer operation's
monotonicity carrying the inner one's inclusion. -/
theorem DependencyPreserving.comp {D α β γ : Type} {A : Set β → Set γ} {B : Set α → Set β}
    {e : D → Set α} {e₁ : D → Set β} {e₂ : D → Set γ} (hA : Monotone A)
    (hB : DependencyPreserving B e e₁) (hAe : DependencyPreserving A e₁ e₂) :
    DependencyPreserving (A ∘ B) e e₂ := by
  intro d x hx
  exact hAe d (hA (hB d) hx)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
