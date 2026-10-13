module

public import CORALean.Specification.Specification

@[expose] public section

/-!
# A specification holds of a union when it holds of each part

`holds_of_outer` shrinks a checked set; this grows it, by the same case split.
A safe set (and an invariant, the same test) closed downward under `⊆` is
closed under `Set.union_subset` once both halves land inside it, and an
unsafe set each half avoids is avoided by their union, by `Disjoint.union_left`.

The binary case a two-part split needs; `HoldsIUnion` is the indexed form
`NeuralNetwork.holds_of_split` actually applies.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   24-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {ContSet α : Type} [CORALean.ContSet ContSet α] {X Y : Set α}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Specification.holds_union (spec : Specification ContSet) (hX : spec.Holds X)
    (hY : spec.Holds Y) : spec.Holds (X ∪ Y) := by -- --- PROOF ---
  obtain ⟨s, k⟩ := spec
  cases k
  · exact Set.union_subset hX hY
  · exact hX.union_left hY
  · exact Set.union_subset hX hY

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
