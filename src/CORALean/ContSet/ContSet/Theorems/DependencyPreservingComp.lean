module

public import CORALean.ContSet.ContSet.Definitions.IsDependencyPreserving
public import Mathlib.Order.BourbakiWitt

@[expose] public section

/-!
# [1, Lemma 2]: a composition preserves dependencies

Two steps joined: `B` carries the set with evaluation function `e` to the one with `e₁`, `A` carries
that to `e₂`, each preserving dependencies, so `A ∘ B` does. `hA` is the monotonicity [1] states
once for all the set operations it uses — its property (6) — and [1, Lemma 2]'s proof spends it at
exactly the step `hA` is spent at here.

[1, Lemma 1] — that a composition keeps (6) — is Mathlib's `Monotone.comp`, (6) being `Monotone` at
`Set α` ordered by `⊆`. That is why monotonicity is a hypothesis here and never a conclusion.

## Inputs
* `D` – parameter domain
* `α` – source set type
* `β` – middle set type
* `γ` – target set type
* `A` – outer operation
* `B` – inner operation
* `e` – evaluation function of the source
* `e₁` – evaluation function of the middle
* `e₂` – evaluation function of the target

## Hypotheses
* `hA` – `A` monotone
* `hB` – `B` preserves dependencies
* `hAe` – `A` preserves dependencies

## Conclusion
* `A ∘ B` preserves dependencies

## References

* [1] [N. Kochdumper, B. Schürmann and M. Althoff. "Utilizing Dependencies to Obtain Subsets of
      Reachable Sets". Proceedings of the 23rd International Conference on Hybrid Systems:
      Computation and Control,
      2020.](../../../../../references/2020/kochdumper-hscc-utilizing-dependencies.md)
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
theorem IsDependencyPreserving.comp {D α β γ : Type} {A : Set β → Set γ} {B : Set α → Set β}
    {e : D → Set α} {e₁ : D → Set β} {e₂ : D → Set γ} (hA : Monotone A)
    (hB : IsDependencyPreserving B e e₁) (hAe : IsDependencyPreserving A e₁ e₂) :
    IsDependencyPreserving (A ∘ B) e e₂ := by
  intro d x hx
  exact hAe d (hA (hB d) hx)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
