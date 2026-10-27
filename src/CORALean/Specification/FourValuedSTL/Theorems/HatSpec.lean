module

public import CORALean.Specification.FourValuedSTL.Definitions.Hat
public import Mathlib.Data.NNReal.Defs

@[expose] public section

/-!
# What the set-based predicate says of a state

If `â(X')` is `⊤` every state of `X'` satisfies `a`, and if it is `⊥` none does: for a state
`x ∈ X'`, `â(X') = ⊤` gives `a x` and `â(X') = ⊥` gives `¬a x`
([1, Sec. 3 (predicate)]). This is the base case of [1, Thm. 1]: `â(R(t)) = ⊤` gives `a(ξ(t)) = ⊤`
for every execution with `ξ(t) ∈ R(t)`.

## Inputs
* `X` – state type
* `a` – atomic predicate
* `S` – set of states
* `x` – state

## Hypotheses
* `hx` – the state lies in the set

## Conclusion
* a true set-based predicate holds at the state, a false one fails

## References

* [1] [F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". Computer Aided Verification,
      2024.](../../../../../references/2024/lercher-cav-four-valued-stl.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal


-- =======================================  MAIN THEOREM  ======================================= --

theorem FourValuedSTL.hat_spec {X : Type} {a : X → Prop} {S : Set X} {x : X}
    (hx : x ∈ S) : -- --- CONCL ---
    (FourValuedSTL.hat a S = Kleene.tt → a x) ∧
      (FourValuedSTL.hat a S = Kleene.ff → ¬ a x) := by -- --- PROOF ---
  classical
  unfold FourValuedSTL.hat
  by_cases h1 : S.Nonempty ∧ S ⊆ {x | a x}
  · -- all states satisfy `a`
    rw [if_pos h1]
    exact ⟨fun _ => h1.2 hx, nofun⟩
  rw [if_neg h1]
  by_cases h2 : S.Nonempty ∧ S ∩ {x | a x} = ∅
  · -- no state satisfies `a`
    rw [if_pos h2]
    refine ⟨nofun, fun _ hax => ?_⟩
    have : x ∈ S ∩ {x | a x} := ⟨hx, hax⟩
    rw [h2.2] at this
    exact this
  rw [if_neg h2]
  exact ⟨nofun, nofun⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
