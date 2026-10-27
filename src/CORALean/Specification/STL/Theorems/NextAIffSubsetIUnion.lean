module

public import CORALean.Specification.STL.Definitions.Halfspace
public import CORALean.Specification.STL.Definitions.RTL

@[expose] public section

/-!
# Checking `Aϱ` at a time is a polytope inclusion

[1, Sec. 5]: with `ϱ` in disjunctive normal form, `R ⊨ᵣ X_t Aϱ` is the inclusion `R(t) ⊆ ⋃ᵢ polyᵢ`
of the reachable set at `t` in the union of the polytopes, each `polyᵢ` a conjunction of
halfspaces: what a polytope library checks.

## Inputs
* `R` – reach sequence
* `t` – time
* `ϱ` – predicate
* `dnf` – disjunctive normal form

## Hypotheses
* `h` – the predicate and the normal form agree

## Conclusion
* next of the predicate holds iff the reach set lies in the polytope union

## References

* [1] [H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". Automated Technology for Verification and Analysis,
      2016.](../../../../../references/2016/roehm-atva-stl-model-checking.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem RTL.next_A_iff_subset_iUnion {R : ℝ≥0 → Set α} (t : ℝ≥0) (ϱ : Pform α)
    (dnf : List (List (STL.Halfspace α))) (h : ∀ x, ϱ.Satisfies x ↔ STL.Dnf.Holds dnf x) :
    (RTL.Formula.next t (.A ϱ)).Satisfies R ↔
      R t ⊆ ⋃ cl ∈ dnf, {x | ∀ hs ∈ cl, hs.Holds x} := by
  -- a state of `R(t)` satisfies `ϱ` iff it lies in one of the polytopes
  simp only [RTL.Formula.Satisfies, Time.shift, zero_add, Set.subset_def, Set.mem_iUnion,
    Set.mem_setOf_eq, h, STL.Dnf.Holds, exists_prop]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
