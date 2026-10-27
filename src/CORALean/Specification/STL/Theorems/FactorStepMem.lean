module

public import CORALean.Specification.STL.Operations.FactorStep

@[expose] public section

/-!
# A factor that enters a polytope stays in the pass of [1, Alg. 2]

If `α` is in a polytope of `V` and the state `ξ` it gives, which is in `R̃`, is in one of the
polytopes `P_hjkl`, then `α` is in a polytope of `STL.factorStep` (lines 7-13 of [1, Alg. 2]):
`meets` finds the intersection, `α` is in the unsafe factors of that polytope by [1, Prop. 2]
(`hU`), and a polytope holding `α` is not empty. `meets` answering `false` means no intersection,
`isEmpty` answering `true` an empty polytope; neither is trusted otherwise.

## Inputs
* `Rj` – reachable set
* `Pjk` – polytopes of the formula
* `unsafeSet` – unsafe factor set of a polytope
* `meets` – set intersection test
* `isEmpty` – emptiness test
* `V` – accumulated unsafe polytopes
* `α` – factor
* `ξ` – solution for the factor

## Hypotheses
* `hR` – the solution lies in the reachable set
* `hU` – a solution in a polytope puts its factor in the unsafe set
* `hmeets` – a negative test means the sets are disjoint
* `hempty` – a positive emptiness test means the set is empty
* `hP` – the solution lies in one of the polytopes
* `hV` – the factor lies in one of the accumulated polytopes

## Conclusion
* the factor lies in a polytope after the pass

## References

* [1] [N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, 2024.](../../../../../references/2024/kochdumper-nahs-stl-lti-verification.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S X : Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.exists_mem_factorStep (Rj : Set S) (Pjk : List (Set S)) (unsafeSet : Set S → Set X)
    (meets : Set S → Set S → Bool) (isEmpty : Set X → Bool) (V : List (Set X)) (α : X) (ξ : S)
    (hR : ξ ∈ Rj) (hU : ∀ Pl, ξ ∈ Pl → α ∈ unsafeSet Pl)
    (hmeets : ∀ A B, meets A B = false → A ∩ B = ∅)
    (hempty : ∀ v, isEmpty v = true → v = ∅) (hP : ∃ Pl ∈ Pjk, ξ ∈ Pl)
    (hV : ∃ v ∈ V, α ∈ v) : -- --- CONCL ---
    ∃ v ∈ STL.factorStep Rj Pjk unsafeSet meets isEmpty V, α ∈ v := by -- --- PROOF ---
  obtain ⟨v, hv, hαv⟩ := hV
  obtain ⟨Pl, hPl, hξ⟩ := hP
  -- `Rj` meets `Pl`, at `ξ`
  have hm : meets Rj Pl = true := by
    by_contra hne
    have h1 := hmeets _ _ (by simpa using hne)
    have h2 : ξ ∈ Rj ∩ Pl := ⟨hR, hξ⟩
    rw [h1] at h2; exact h2
  refine ⟨v ∩ unsafeSet Pl, ?_, hαv, hU Pl hξ⟩
  simp only [STL.factorStep, List.mem_filter, STL.factorMeet, List.mem_flatMap, List.mem_map]
  refine ⟨⟨v, hv, unsafeSet Pl, ⟨Pl, ⟨hPl, hm⟩, rfl⟩, rfl⟩, ?_⟩
  -- the meet holds `α`, so it is not empty
  simp only [Bool.not_eq_true']
  by_contra hne
  have h1 := hempty _ (by simpa using hne)
  have h2 : α ∈ v ∩ unsafeSet Pl := ⟨hαv, hU Pl hξ⟩
  rw [h1] at h2; exact h2

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
