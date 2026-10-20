module

public import CORALean.ContSet.Polygon.Float.Operations.IsequalPieces
public import CORALean.ContSet.Polygon.Float.Theorems.PieceSubsetSound
public import CORALean.ContSet.SetUnion.Theorems.Basic

@[expose] public section

/-!
# A `true` from `Polygon.isequalPieces` proves the regions equal

Each piece of either polygon lies in a piece of the other (`Polygon.pieceSubset_sound`), so
each region lies in the other.

## Inputs
* `P` – polygon
* `Q` – polygon

## Hypotheses
* `h` – `Polygon.isequalPieces P Q` holds

## Conclusion
* `P` and `Q` have the same region
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- One direction: every piece of `P` inside some piece of `Q`. -/
theorem Polygon.aux_subset_of_all {P Q : Polygon 𝕋}
    (h : ∀ p ∈ P.sets, ∃ q ∈ Q.sets, Polygon.pieceSubset p q = true) :
    ContSet.construct P ⊆ ContSet.construct Q := by
  intro x hx
  obtain ⟨p, hp, hxp⟩ := SetUnion.mem_construct.mp hx
  obtain ⟨q, hq, hpq⟩ := h p hp
  exact SetUnion.mem_construct.mpr ⟨q, hq, Polygon.pieceSubset_sound hpq hxp⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.isequalPieces_sound {P Q : Polygon 𝕋} (h : Polygon.isequalPieces P Q = true) :
    ContSet.construct P = ContSet.construct Q := by
  simp only [Polygon.isequalPieces, Bool.and_eq_true, List.all_eq_true, List.any_eq_true] at h
  exact Set.Subset.antisymm (Polygon.aux_subset_of_all h.1) (Polygon.aux_subset_of_all h.2)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
