module

public import CORALean.HybridDynamics.Operations.LocationPotOut

@[expose] public section

/-!
# `Location.potOut` keeps every state in the invariant

A state of set `k` that lies in the invariant is still held by entry `k` of the result, which
exists: the only set dropped is a last one certified disjoint from the invariant, and the cut
set holds the state, so it could not have been disjoint. Outer, not exact: `Intersection`
over-approximates.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {L 𝕋 : Type} [Scalar 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

omit [Scalar 𝕋] in
/-- A state of `Rs[k]` in the invariant lies in the `k`-th set of `potOut`. -/
theorem Location.potOut_outer [∀ n, Intersection (S n) (Vec ℝ n)]
    [∀ n, IsDisjoint (S n) (S n)] (ℓ : Location S S L 𝕋 n) (Rs : List (S n))
    (minInd maxInd : List ℕ) {k : ℕ} (hk : k < Rs.length) {x : Vec ℝ n}
    (hx : x ∈ construct Rs[k]) (hinv : x ∈ construct ℓ.inv) :
    ∃ h : k < (ℓ.potOut Rs minInd maxInd).length,
      x ∈ construct (ℓ.potOut Rs minInd maxInd)[k] := by -- --- PROOF ---
  unfold Location.potOut
  set cut := Rs.mapIdx fun k R =>
    if (minInd.zip maxInd).any (fun (a, b) => max a 1 ≤ k + 1 && k + 1 ≤ b)
    then Intersection.intersection ℓ.inv R else R with hcut
  have hlen : cut.length = Rs.length := by simp [hcut]
  -- the cut keeps `x`
  have hxc : x ∈ construct (cut[k]'(by omega)) := by
    simp only [hcut, List.getElem_mapIdx]
    split
    · exact Intersection.intersection_outer _ _ ⟨hinv, hx⟩
    · exact hx
  cases hl : cut.getLast? with
  | none =>
    simp only [hl]
    exact ⟨by omega, hxc⟩
  | some last =>
    simp only [hl]
    split
    · -- the last set is certified disjoint from the invariant
      rename_i hdis
      by_cases hlast : k + 1 = cut.length
      · exfalso
        have hlst : cut.getLast? = some (cut[k]'(by omega)) := by
          rw [List.getLast?_eq_getElem?, show cut.length - 1 = k by omega]
          exact List.getElem?_eq_getElem _
        rw [hl] at hlst
        cases hlst
        exact Set.disjoint_left.mp (IsDisjoint.isDisjoint_sound _ _ hdis) hxc hinv
      · have hk' : k < cut.dropLast.length := by rw [List.length_dropLast]; omega
        exact ⟨hk', by rw [List.getElem_dropLast]; exact hxc⟩
    · exact ⟨by omega, hxc⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
