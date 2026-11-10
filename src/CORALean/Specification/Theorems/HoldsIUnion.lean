module

public import CORALean.Specification.Specification

@[expose] public section

/-!
# A specification holds of an indexed union when it holds of each part

The form `NeuralNetwork.holds_of_split` actually needs, `ι` arbitrary.
No case needs finiteness, and none needs `ι` nonempty: `⋃ i, 𝒳 i` over an
empty `ι` is `∅`, which sits inside every safe set (and every invariant, the
same test) and misses every unsafe one, so `h`, vacuous, still closes the
goal — no hypothesis on `ι` is dropped here for want of one, it is simply not
needed.

## Inputs
* `ι` – index type of the parts
* `spec` – specification
* `𝒳` – parts of the set

## Hypotheses
* `h` – the specification holds of each part

## Conclusion
* the specification holds of the union
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   24-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {ContSet α : Type} [ContSetLike ContSet α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Specification.holds_iUnion {ι : Type} (spec : Specification ContSet) {𝒳 : ι → Set α}
    (h : ∀ i, spec.Holds (𝒳 i)) : -- --- CONCL ---
    spec.Holds (⋃ i, 𝒳 i) := by -- --- PROOF ---
  obtain ⟨s, k⟩ := spec
  cases k
  · exact Set.iUnion_subset h
  · exact Set.disjoint_iUnion_left.mpr h
  · exact Set.iUnion_subset h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
