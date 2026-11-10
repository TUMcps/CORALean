module

public import CORALean.ContSet.ContSet.Theorems.Basic
public import CORALean.Specification.Specification
public import CORALean.Specification.Theorems.Basic
public import CORALean.Specification.Operations.Custom

@[expose] public section

/-!
# `Specification.holds_custom_iff`

A custom specification holds on `𝒳` exactly when its predicate does: the predicate is downward
closed and closed under unions, so the largest set it admits is the union of all of them.

## Inputs
* `p` – property of sets
* `𝒳` – set of points

## Hypotheses
* `mono` – the property is monotone
* `iUnionClosed` – the property is closed under unions

## Conclusion
* the custom specification holds iff the property holds
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet ContSetLike

variable {ContSet α : Type} [ContSetLike ContSet α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Specification.holds_custom_iff (p : Set α → Prop)
    (mono : ∀ {𝒳 O : Set α}, 𝒳 ⊆ O → p O → p 𝒳)
    (iUnionClosed : ∀ {ι : Type} {𝒳 : ι → Set α}, (∀ i, p (𝒳 i)) → p (⋃ i, 𝒳 i))
    {𝒳 : Set α} : (Specification.custom p mono iUnionClosed).Holds 𝒳 ↔ p 𝒳 := by
  rw [Specification.custom, Specification.holds_safeSet, ContSet.toSet_set]
  refine ⟨fun hsub => mono hsub (iUnionClosed fun h => h.2), fun hpX => ?_⟩
  exact Set.subset_iUnion (fun h : {S : Set α // p S} => h.1) ⟨𝒳, hpX⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
