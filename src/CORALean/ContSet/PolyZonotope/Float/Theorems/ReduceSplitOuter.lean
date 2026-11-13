module

public import CORALean.ContSet.Conversion.Float.Theorems.PolyZonotopeZonotopeFoldContains
public import CORALean.ContSet.Interval.Float.Theorems.OriginExact
public import CORALean.ContSet.PolyZonotope.Float.Operations.ReduceSplit
public import CORALean.ContSet.PolyZonotope.Float.Theorems.ConstructOuter
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.PolyZonotope.Float.Theorems.OfIndepOuter
public import CORALean.ContSet.PolyZonotope.Float.Theorems.PlusOuter
public import CORALean.ContSet.PolyZonotope.Float.Theorems.Basic
public import CORALean.ContSet.Zonotope.Float.Theorems.ReduceGirardOuter

@[expose] public section

/-!
# CORA's reduction at a split of the generators encloses

A point at the factors `a` is the kept generators at `a` plus the removed ones at `a`, the two
index lists being a partition. The removed part is a point of the polynomial zonotope about the
origin, hence of its constructed form, of the zonotope of that, and of the Girard reduction of it;
the kept part and the reduction add, as the independent sum does; dropping the unused factors
encloses. Where the lists are no partition, the set is only stripped of its unused factors.

## Inputs
* `pZ` – polynomial zonotope
* `kD`, `rD`, `kI`, `rI` – the generators kept and removed
* `order` – the order of the merged exponent columns of the removed part

## Hypotheses
* none

## Conclusion
* the set is contained in the reduced one
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A sum over `Fin h` split along two index lists that partition `0, …, h-1`. -/
private theorem PolyZonotope.aux_sum_split {α : Type} [AddCommMonoid α] {h : ℕ}
    (kD rD : Array ℕ) (hp : (kD.toList ++ rD.toList).Perm (List.range h))
    (hk : ∀ t : Fin kD.size, kD[t.val] < h) (hr : ∀ t : Fin rD.size, rD[t.val] < h)
    (F : Fin h → α) : -- --- CONCL ---
    ∑ l, F l = ∑ t : Fin kD.size, F ⟨kD[t.val], hk t⟩
      + ∑ t : Fin rD.size, F ⟨rD[t.val], hr t⟩ := by -- --- PROOF ---
  classical
  -- the family extended by zero to the naturals, summed over `range h` and over the lists
  let F' : ℕ → α := fun m => if hm : m < h then F ⟨m, hm⟩ else 0
  have hF' : ∀ m (hm : m < h), F' m = F ⟨m, hm⟩ := fun m hm => by simp [F', hm]
  have h1 : ∑ l, F l = ∑ m ∈ Finset.range h, F' m := by
    rw [← Fin.sum_univ_eq_sum_range F' h]
    exact Finset.sum_congr rfl fun l _ => (hF' l.val l.isLt).symm
  have h2 : ∑ m ∈ Finset.range h, F' m = ((List.range h).map F').sum := by
    rw [← List.toFinset_range, List.sum_toFinset F' (List.nodup_range)]
  have h3 : ((List.range h).map F').sum = ((kD.toList ++ rD.toList).map F').sum :=
    (hp.map F').sum_eq.symm
  have h4 : ∀ a : Array ℕ, (ha : ∀ t : Fin a.size, a[t.val] < h) →
      (a.toList.map F').sum = ∑ t : Fin a.size, F ⟨a[t.val], ha t⟩ := by
    intro a ha
    rw [← List.sum_ofFn]
    congr 1
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp [hF' _ (ha ⟨i, by simpa using h1⟩)]
  rw [h1, h2, h3, List.map_append, List.sum_append, h4 kD hk, h4 rD hr]


-- =======================================  MAIN THEOREM  ======================================= --

set_option maxHeartbeats 400000 in -- the one proof unfolds the whole reduction at once
theorem PolyZonotope.reduceSplit_outer (pZ : PolyZonotope (Vec 𝕋 n)) (kD rD kI rI : Array ℕ)
    (order : ℕ → Array (Array ℕ) → Array ℕ) : -- --- CONCL ---
    pZ.toSet ⊆ (pZ.reduceSplit kD rD kI rI order).toSet := by -- --- PROOF ---
  unfold PolyZonotope.reduceSplit
  split_ifs with hv
  swap
  · exact PolyZonotope.compactFactors_outer pZ
  obtain ⟨hpD, hpI⟩ := hv
  have hD : ∀ t : Fin kD.size, kD[t.val] < pZ.h := fun t =>
    List.mem_range.mp (hpD.mem_iff.mp (by simp))
  have hD' : ∀ t : Fin rD.size, rD[t.val] < pZ.h := fun t =>
    List.mem_range.mp (hpD.mem_iff.mp (by simp))
  have hI : ∀ t : Fin kI.size, kI[t.val] < pZ.q := fun t =>
    List.mem_range.mp (hpI.mem_iff.mp (by simp))
  have hI' : ∀ t : Fin rI.size, rI[t.val] < pZ.q := fun t =>
    List.mem_range.mp (hpI.mem_iff.mp (by simp))
  refine subset_trans ?_ (PolyZonotope.compactFactors_outer _)
  refine subset_trans ?_ (PolyZonotope.plus_outer _ _)
  rintro _ ⟨z, hz, e, he, rfl⟩
  obtain ⟨a, β, ha, hβ, hx⟩ := PolyZonotope.mem_nominalSet_iff.mp hz
  -- the exact sums, split along the lists
  have hsD : ∀ i, ∑ l, toReal (pZ.G l i) * Real.PolyZonotope.monomial pZ.E a l
      = ∑ t : Fin kD.size, toReal (pZ.G ⟨kD[t.val], hD t⟩ i)
          * Real.PolyZonotope.monomial pZ.E a ⟨kD[t.val], hD t⟩
        + ∑ t : Fin rD.size, toReal (pZ.G ⟨rD[t.val], hD' t⟩ i)
          * Real.PolyZonotope.monomial pZ.E a ⟨rD[t.val], hD' t⟩ := fun i =>
    PolyZonotope.aux_sum_split kD rD hpD hD hD'
      (fun l => toReal (pZ.G l i) * Real.PolyZonotope.monomial pZ.E a l)
  have hsI : ∀ i, ∑ j, toReal (pZ.GI j i) * β j
      = ∑ t : Fin kI.size, toReal (pZ.GI ⟨kI[t.val], hI t⟩ i) * β ⟨kI[t.val], hI t⟩
        + ∑ t : Fin rI.size, toReal (pZ.GI ⟨rI[t.val], hI' t⟩ i) * β ⟨rI[t.val], hI' t⟩ := fun i =>
    PolyZonotope.aux_sum_split kI rI hpI hI hI' (fun j => toReal (pZ.GI j i) * β j)
  -- the kept part at the factors, and the removed part
  obtain ⟨nK, hnK⟩ : ∃ nK : Vec ℝ n, ∀ i, nK i = toReal (pZ.c i)
      + ∑ t : Fin kD.size, toReal (pZ.G ⟨kD[t.val], hD t⟩ i)
          * Real.PolyZonotope.monomial pZ.E a ⟨kD[t.val], hD t⟩
      + ∑ t : Fin kI.size, toReal (pZ.GI ⟨kI[t.val], hI t⟩ i) * β ⟨kI[t.val], hI t⟩ :=
    ⟨fun i => toReal (pZ.c i)
      + ∑ t : Fin kD.size, toReal (pZ.G ⟨kD[t.val], hD t⟩ i)
          * Real.PolyZonotope.monomial pZ.E a ⟨kD[t.val], hD t⟩
      + ∑ t : Fin kI.size, toReal (pZ.GI ⟨kI[t.val], hI t⟩ i) * β ⟨kI[t.val], hI t⟩,
      fun i => rfl⟩
  -- the removed generators, summed
  obtain ⟨r, hr⟩ : ∃ r : Vec ℝ n, ∀ i, r i = ∑ t : Fin rD.size, toReal (pZ.G ⟨rD[t.val], hD' t⟩ i)
          * Real.PolyZonotope.monomial pZ.E a ⟨rD[t.val], hD' t⟩
      + ∑ t : Fin rI.size, toReal (pZ.GI ⟨rI[t.val], hI' t⟩ i) * β ⟨rI[t.val], hI' t⟩ :=
    ⟨fun i => ∑ t : Fin rD.size, toReal (pZ.G ⟨rD[t.val], hD' t⟩ i)
          * Real.PolyZonotope.monomial pZ.E a ⟨rD[t.val], hD' t⟩
      + ∑ t : Fin rI.size, toReal (pZ.GI ⟨rI[t.val], hI' t⟩ i) * β ⟨rI[t.val], hI' t⟩,
      fun i => rfl⟩
  -- the kept part, the reduced removed part, and their sum
  refine Set.mem_add.mpr ⟨nK + e, ?_, r, ?_, ?_⟩
  · exact Set.mem_add.mpr ⟨nK, PolyZonotope.mem_nominalSet_iff.mpr
      ⟨a, fun t => β ⟨kI[t.val], hI t⟩, ha, fun t => hβ _, fun i => hnK i⟩, e, he, rfl⟩
  · refine Zonotope.ofIndep_outer _ (Zonotope.reduceGirard_outer _ _
      (PolyZonotope.zonotopeFold_contains _ (PolyZonotope.construct_outer _ _ ?_)))
    have h0 : (0 : Vec ℝ n) ∈ (Interval.origin n : Interval (Vec 𝕋 n)).toSet := by
      rw [Interval.origin_exact]
      exact Set.mem_singleton _
    refine Set.mem_add.mpr ⟨r, PolyZonotope.mem_nominalSet_iff.mpr
      ⟨a, fun t => β ⟨rI[t.val], hI' t⟩, ha, fun t => hβ _, fun i => ?_⟩, 0, h0, add_zero r⟩
    show r i = toReal (zero : 𝕋) + _ + _
    rw [toReal_zero, zero_add, hr i]
    rfl
  · funext i
    show nK i + e i + r i = z i + e i
    rw [hx i, hsD i, hsI i, hnK i, hr i]
    ring

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
