module

public import CORALean.ContSet.PolyZonotope.Float.Operations.TabAt
public import Mathlib.Data.List.NodupEquivFin

@[expose] public section

/-!
# The `j`-th element of a filtered `finRange` is the finset's

A finset of `Fin h` listed by filtering `List.finRange h` with its own
membership test is listed in increasing order, so reading the list at `j` is
what `orderIsoOfFin` answers. `orderEmbOfFin_unique` is the only strictly
increasing enumeration of a finset, and a filtered `finRange` is one.

## Inputs
* `s` – finite index set
* `P` – membership test
* `j` – element number

## Hypotheses
* `hP` – the test decides membership

## Conclusion
* the table entry is that element of the set
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {h : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.tabAt_filter (s : Finset (Fin h)) (P : Fin h → Bool)
    (hP : ∀ x, P x = true ↔ x ∈ s) (j : Fin s.card) :
    PolyZonotope.tabAt s ((List.finRange h).filter P).toArray j
      = s.orderIsoOfFin rfl j := by -- --- PROOF ---
  set L := (List.finRange h).filter P with hL
  have hmem : ∀ x, x ∈ L ↔ x ∈ s := fun x => by
    rw [hL, List.mem_filter, ← hP x]; simp
  have hnd : L.Pairwise (· < ·) := (List.pairwise_lt_finRange h).filter _
  have hlen : L.length = s.card := by
    have : L.Nodup := hnd.imp ne_of_lt
    rw [← List.toFinset_card_of_nodup this]
    congr 1
    ext x; simp [hmem]
  -- the table is the list, read at `j`
  have hget : PolyZonotope.tabAt s L.toArray j = L[j.val]'(by rw [hlen]; exact j.isLt) := by
    show L.toArray.getD j.val _ = _
    rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray,
      List.getElem?_eq_getElem (by rw [hlen]; exact j.isLt)]
    rfl
  rw [hget]
  have := Finset.orderEmbOfFin_unique (s := s) (k := s.card) rfl
    (f := fun j => L[j.val]'(by rw [hlen]; exact j.isLt))
    (fun x => (hmem _).1 (List.getElem_mem _))
    (fun a b hab => List.pairwise_iff_getElem.1 hnd _ _ _ _ hab)
  exact (congrFun this j).trans (by simp)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
