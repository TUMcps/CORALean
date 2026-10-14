module

public import CORALean.Specification.PointSegmentSignal.Operations.CutAtFirstFallingEdge
public import CORALean.Specification.PointSegmentSignal.Theorems.Basic
public import CORALean.Specification.PointSegmentSignal.Theorems.MemMatlabFind
public import Mathlib.Algebra.Order.Group.Nat

@[expose] public section

/-!
# The first falling edge of a Boolean array

`find(~x(2:end) & x(1:end-1),1,'first')` of a Boolean array is its first falling edge: with no edge,
`x` never falls; otherwise the edge `i` has `x(i)` true and `x(i + 1)` false, and `x` does not fall
before it.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- The first index where `true` is followed by `false`. -/
theorem List.first_falling_edge (v : List Bool) :
    ((List.matlabFind id (List.zipWith (fun a b => !b && a) v v.tail)).head? = none →
      ∀ p, 1 ≤ p → p < v.length → v.getD (p - 1) false = true → v.getD p false = true) ∧
    ∀ i, (List.matlabFind id (List.zipWith (fun a b => !b && a) v v.tail)).head? = some i →
      1 ≤ i ∧ i < v.length ∧ v.getD (i - 1) false = true ∧ v.getD i false = false ∧
      ∀ p, 1 ≤ p → p < i → v.getD (p - 1) false = true →
        v.getD p false = true := by -- --- PROOF ---
  -- the flags: an entry of `~x(2:end) & x(1:end-1)`
  have hz : ∀ j, 1 ≤ j → j < v.length → (List.zipWith (fun a b => !b && a) v v.tail)[j - 1]? =
      some (!(v.getD j false) && v.getD (j - 1) false) := fun j h1 h2 => by
    have e : j - 1 + 1 = j := by omega
    simp [List.getElem?_zipWith, List.getElem?_tail, e, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem h2, List.getElem?_eq_getElem (show j - 1 < v.length by omega)]
  have hlen : (List.zipWith (fun a b => !b && a) v v.tail).length = v.length - 1 := by simp
  -- a flag is set where the array falls
  have hflag : ∀ j, j ∈ List.matlabFind id (List.zipWith (fun a b => !b && a) v v.tail) ↔
      1 ≤ j ∧ j < v.length ∧ v.getD (j - 1) false = true ∧ v.getD j false = false := by
    intro j
    rw [List.mem_matlabFind]
    constructor
    · rintro ⟨h1, h2, h3⟩
      have hl : j < v.length := by omega
      have h5 := Option.some.inj ((List.getElem?_eq_getElem h2).symm.trans (hz j h1 hl))
      rw [h5] at h3
      simp only [id, Bool.and_eq_true, Bool.not_eq_true'] at h3
      exact ⟨h1, hl, h3.2, h3.1⟩
    · rintro ⟨h1, hl, h2, h3⟩
      refine ⟨h1, by omega, ?_⟩
      have h5 := Option.some.inj ((List.getElem?_eq_getElem (show j - 1 <
        (List.zipWith (fun a b => !b && a) v v.tail).length by omega)).symm.trans (hz j h1 hl))
      rw [h5, h3, h2]
      rfl
  refine ⟨fun hnone p hp1 hp2 hp => ?_, fun i hi => ?_⟩
  · -- no flag is set, so the array does not fall at `p`
    by_contra hne
    have hf : v.getD p false = false := by simpa using hne
    have hpL := (hflag p).2 ⟨hp1, hp2, hp, hf⟩
    rw [List.head?_eq_none_iff.1 hnone] at hpL
    simp at hpL
  · -- the first flag is the least one
    obtain ⟨h1, h2, h3, h4⟩ := (hflag i).1 (List.mem_of_mem_head? hi)
    refine ⟨h1, h2, h3, h4, fun p hp1 hp2 hp => ?_⟩
    by_contra hne
    have hf : v.getD p false = false := by simpa using hne
    have hpL := (hflag p).2 ⟨hp1, by omega, hp, hf⟩
    have hsort := List.pairwise_matlabFind id (List.zipWith (fun a b => !b && a) v v.tail)
    obtain ⟨tl, htl⟩ := List.head?_eq_some_iff.1 hi
    rw [htl] at hpL hsort
    rcases List.mem_cons.1 hpL with rfl | hp'
    · exact lt_irrefl _ hp2
    · exact absurd ((List.pairwise_cons.1 hsort).1 p hp') (not_lt.2 hp2.le)
end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
