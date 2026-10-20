module

public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Hom.Defs

@[expose] public section

/-!
# A preimage plus the image of a section is the preimage of the sum

For `L : α → β` with a section `S`, the points of `N` pulled back along `L`, shifted by
`S e` for `e ∈ E`, are the points whose image lies in `N + E`. This is why padding or lifting
a polytope that carries an error box is exact: the box is padded or lifted the same way, with
zeros in the new coordinates. A constraint `C` on the new coordinates may ride along, if it
does not notice a shift by `S e`.

## Inputs
* `L` – `α →+ β`
* `S` – `β →+ α`
* `N` – set of points
* `E` – set of points
* `C` – set of points

## Hypotheses
* `hLS` – `L` is a left inverse of `S`
* `hC` – adding `S e` to a point does not change membership in `C`

## Conclusion
* A preimage plus the image of a section is the preimage of the sum
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise

variable {α β : Type} [AddCommGroup α] [AddCommGroup β]


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.preimage_inter_add_image (L : α →+ β) (S : β →+ α)
    (hLS : ∀ e, L (S e) = e) (N E : Set β) (C : Set α)
    (hC : ∀ x e, x + S e ∈ C ↔ x ∈ C) : -- --- CONCL ---
    (L ⁻¹' N ∩ C) + S '' E = L ⁻¹' (N + E) ∩ C := by -- --- PROOF ---
  ext x
  constructor
  · rintro ⟨y, ⟨hyN, hyC⟩, _, ⟨e, he, rfl⟩, rfl⟩
    refine ⟨⟨L y, hyN, e, he, ?_⟩, (hC y e).mpr hyC⟩
    simp [hLS]
  · rintro ⟨⟨z, hz, e, he, hx⟩, hxC⟩
    refine ⟨x - S e, ⟨?_, ?_⟩, S e, ⟨e, he, rfl⟩, sub_add_cancel _ _⟩
    · show L (x - S e) ∈ N
      rw [map_sub, hLS, ← hx, add_sub_cancel_right]
      exact hz
    · have := (hC (x - S e) e).mp (by rwa [sub_add_cancel])
      exact this

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
