import CORALean.Specification.Specification

/-!
# A specification holds of an indexed union when it holds of each part

The form `NeuralNetwork.holds_of_split` actually needs, `ι` arbitrary.
No case needs finiteness, and none needs `ι` nonempty: `⋃ i, X i` over an
empty `ι` is `∅`, which sits inside every safe set (and every invariant, the
same test) and misses every unsafe one, so `h`, vacuous, still closes the
goal — no hypothesis on `ι` is dropped here for want of one, it is simply not
needed.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {α : Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Specification.holds_iUnion {ι : Type} (spec : Specification α) {X : ι → Set α}
    (h : ∀ i, spec.Holds (X i)) : spec.Holds (⋃ i, X i) := by -- --- PROOF ---
  obtain ⟨s, k⟩ := spec
  cases k
  · exact Set.iUnion_subset h
  · exact Set.disjoint_iUnion_left.mpr h
  · exact Set.iUnion_subset h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
