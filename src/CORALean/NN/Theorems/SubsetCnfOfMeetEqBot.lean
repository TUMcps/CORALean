module

public import CORALean.ContSet.ContSet.ContSet

@[expose] public section

/-!
# Containment in a CNF formula by meets with its negated clauses

[1, Sec. IV-B (containment)]: for `C = ⋀ᵢ ⋁ⱼ lᵢⱼ`, the abstract element `a` is inside `C` when
`a ⊓ ⋀ⱼ ¬lᵢⱼ = ⊥` for every clause `i`. A point of `γ(a)` outside `C` violates some clause, so
it satisfies every negated literal of it and survives the sound meet, into `γ(⊥) = ∅`.

A literal is anything with a set of points and a negation denoting the complement, so the
statement covers the paper's linear constraints and is not tied to `CatCond`, whose guards are
conjunctions and so not closed under negation. The meet takes a whole conjunction, as the paper's
does.

## Inputs
* `sat` – set a literal denotes
* `neg` – negation of a literal
* `meet` – meet of an abstract element with literals
* `bot` – bottom element
* `a` – abstract element
* `cnf` – formula as a list of clauses

## Hypotheses
* `hneg` – negation denotes the complement
* `hmeet` – the meet contains the intersection
* `hbot` – bottom denotes the empty set
* `h` – the element meets every negated clause to bottom

## Conclusion
* the element's set lies in the formula's set

## References

* [1] [T. Gehr, M. Mirman, D. Drachsler-Cohen, P. Tsankov, S. Chaudhuri and M. Vechev. "AI2: Safety
      and Robustness Certification of Neural Networks with Abstract Interpretation". 2018 IEEE
      Symposium on Security and Privacy (SP), 2018.](../../../../references/2018/gehr-sp-ai2.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S α L : Type} [ContSet S α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every clause of `cnf` holds on `γ(a)` once `a` met with its negation is `⊥`. -/
theorem subset_cnf_of_meet_eq_bot (sat : L → Set α) (neg : L → L)
    (hneg : ∀ l, sat (neg l) = (sat l)ᶜ) (meet : S → List L → S)
    (hmeet : ∀ a ls, construct a ∩ {x | ∀ l ∈ ls, x ∈ sat l} ⊆ construct (meet a ls))
    (bot : S) (hbot : construct bot = ∅) (a : S) (cnf : List (List L))
    (h : ∀ c ∈ cnf, meet a (c.map neg) = bot) : -- --- CONCL ---
    construct a ⊆ {x | ∀ c ∈ cnf, ∃ l ∈ c, x ∈ sat l} := by -- --- PROOF ---
  intro x hx c hc
  by_contra hno
  push Not at hno
  -- `x` satisfies every negated literal of the clause, so it is in the meet, which is `⊥`
  have hin : x ∈ construct (meet a (c.map neg)) := hmeet a _ ⟨hx, fun l hl => by
    obtain ⟨l', hl', rfl⟩ := List.mem_map.mp hl
    rw [hneg]
    exact hno l' hl'⟩
  rw [h c hc, hbot] at hin
  exact hin

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
