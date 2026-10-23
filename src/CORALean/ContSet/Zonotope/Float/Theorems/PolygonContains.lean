module

public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.Interval.Real.Theorems.Convex
public import CORALean.ContSet.VPolytope.Float.Theorems.MemColumnGap
public import CORALean.ContSet.VPolytope.Real.Theorems.ConvexHull
public import CORALean.ContSet.VPolytope.Real.Theorems.PerturbSubset
public import CORALean.ContSet.Zonotope.Float.Operations.Polygon
public import CORALean.ContSet.Zonotope.Float.Theorems.Basic
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Zonotope.Real.Theorems.ConstructSubsetWalk
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_VPolytope
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_VPolytope
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_VPolytope
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalVPolytopeContains
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopeIntervalContains
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopeVPolytopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.HPolytopeIntervalContains
public import CORALean.ContSet.Conversion.Real.Theorems.HPolytopeVPolytopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalVPolytopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.VPolytopeIntervalContains
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeIntervalContains
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeVPolytopeContains

@[expose] public section

/-!
# `Zonotope.polygon` encloses the zonotope

Three steps. The flipped and sorted generators describe the same nominal zonotope (flipping a
generator and reordering the sum change nothing), so the zonotope lies in the sorted one. If the
checks pass, the sorted nominal zonotope lies in the hull of its exact walk corners
(`Zonotope.construct_subset_walk`, the checks being its hypotheses read off the roundings), and
each exact corner lies between its two stored roundings, so in the stored vertex plus the
column-gap box (`VPolytope.mem_columnGap`); the zonotope's own box is added. If a check fails the
result is the box's corners, which enclose by `Zonotope.interval_contains`.

## Inputs
* `Z` – planar zonotope

## Hypotheses
* none

## Conclusion
* zonotope is contained in its polygon
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.polygon_contains (Z : Zonotope (Vec 𝕋 2)) : -- --- CONCL ---
    Z.construct ⊆ Z.polygon.construct := by -- --- PROOF ---
  unfold Zonotope.polygon
  extract_lets Zm hat cross order Zs halfPlane sorted lo hi
  by_cases hc : (halfPlane && sorted) = true
  swap
  · -- a failed check returns the box's corners
    rw [if_neg hc]
    exact (Zonotope.interval_contains Z).trans (Interval.vPolytope_contains _)
  rw [if_pos hc]
  have hc' := Bool.and_eq_true_iff.mp hc
  -- the stored copies read as the zonotopes they copy
  have hGm : ∀ j i, Zm.G j i = Z.G j i := fun j i => by
    show (Zonotope.materialise Z).G j i = _
    simp [Zonotope.materialise]
  have hcs : Zs.c = Z.c := by
    funext i
    show (Zonotope.materialise ⟨Z.h, Zm.c, fun i => hat (order.getD i.val i), Zm.I_error⟩).c i = _
    simp [Zonotope.materialise, Zm]
  have hEs : Zs.I_error = Z.I_error := by
    show Interval.materialise (Interval.materialise Z.I_error) = Z.I_error
    simp
  have hGs : ∀ (j : Fin Z.h) i, Zs.G j i = hat (order.getD j.val j) i := fun j i => by
    show (Zonotope.materialise ⟨Z.h, Zm.c, fun i => hat (order.getD i.val i), Zm.I_error⟩).G j i = _
    simp [Zonotope.materialise]
  -- the sorted list is a permutation of the indices
  have hperm : order.Perm (List.finRange Z.h) := List.mergeSort_perm _ _
  have hlen : order.length = Z.h := by rw [hperm.length_eq, List.length_finRange]
  -- a sum over the sorted order is the sum over the indices
  have hsum : ∀ F : Fin Z.h → ℝ, ∑ i : Fin Z.h, F (order.getD i.val i) = ∑ j, F j := fun F => by
    have hmap : (List.finRange Z.h).map (fun i => F (order.getD i.val i)) = order.map F := by
      refine List.ext_getElem (by simp [hlen]) fun n h1 h2 => ?_
      have hn : n < Z.h := by simpa using h1
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show n < order.length by omega)]
    rw [Fin.sum_univ_def, Fin.sum_univ_def, hmap]
    exact (hperm.map F).sum_eq
  -- a flipped generator is a sign times the original
  have hhat : ∀ j : Fin Z.h, ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
      ∀ i, toReal (hat j i) = s * toReal (Z.G j i) := fun j => by
    by_cases hf : (ltStrict (Zm.G j 1) zero || (!ltStrict zero (Zm.G j 1)
        && ltStrict (Zm.G j 0) zero)) = true
    · refine ⟨-1, Or.inr rfl, fun i => ?_⟩
      have e : hat j i = neg (Zm.G j i) := if_pos hf
      rw [e, toReal_neg, hGm]; ring
    · refine ⟨1, Or.inl rfl, fun i => ?_⟩
      have e : hat j i = Zm.G j i := if_neg hf
      rw [e, hGm]; ring
  choose sgn hsgn hhatR using hhat
  have hsq : ∀ j, sgn j * sgn j = 1 := fun j => by rcases hsgn j with h | h <;> rw [h] <;> norm_num
  have habs : ∀ j (b : ℝ), |b| ≤ 1 → |sgn j * b| ≤ 1 := fun j b hb => by
    rcases hsgn j with h | h <;> rw [h] <;> simpa using hb
  -- the zonotope lies in the sorted one
  have hS : Z.construct ⊆ Zs.construct := by
    rintro _ ⟨y, hy, e, he, rfl⟩
    refine ⟨y, ?_, e, ?_, rfl⟩
    swap
    · show e ∈ Zs.I_error.construct
      rw [hEs]; exact he
    obtain ⟨β, hβ, hz⟩ := Zonotope.mem_nominalSet_iff.mp hy
    -- the coefficients follow the generators to their new places and signs
    refine Zonotope.mem_nominalSet_iff.mpr
      ⟨fun j => sgn (order.getD j.val j) * β (order.getD j.val j), fun j => habs _ _ (hβ _),
        fun i => ?_⟩
    rw [hz i, hcs]
    congr 1
    rw [← hsum fun j => toReal (Z.G j i) * β j]
    refine Finset.sum_congr rfl fun j _ => ?_
    show toReal (Z.G (order.getD j.val j) i) * β (order.getD j.val j)
      = toReal (Zs.G j i) * (sgn (order.getD j.val j) * β (order.getD j.val j))
    rw [hGs, hhatR]
    linear_combination (-(toReal (Z.G (order.getD j.val j) i) * β (order.getD j.val j))) * hsq _
  -- the checks, read as the hypotheses of the real theorem
  obtain ⟨hhalf, hsorted⟩ := hc'
  simp only [halfPlane, List.all_eq_true, List.mem_finRange, forall_const, Bool.and_eq_true,
    Bool.or_eq_true] at hhalf
  simp only [sorted, List.all_eq_true, List.mem_finRange, forall_const, Bool.or_eq_true,
    Bool.not_eq_true'] at hsorted
  have hH1 : ∀ j, 0 ≤ (InflatedContSet.nominal Zs).G j 1 ∧
      (0 < (InflatedContSet.nominal Zs).G j 1 ∨ 0 ≤ (InflatedContSet.nominal Zs).G j 0) :=
    fun j => by
    obtain ⟨a, b | b⟩ := hhalf j
    · exact ⟨by have h := toReal_le_of_le a; rw [toReal_zero] at h; exact h,
        Or.inl (by have h := toReal_lt_of_ltStrict b; rw [toReal_zero] at h; exact h)⟩
    · exact ⟨by have h := toReal_le_of_le a; rw [toReal_zero] at h; exact h,
        Or.inr (by have h := toReal_le_of_le b; rw [toReal_zero] at h; exact h)⟩
  have hH2 : ∀ i j : Fin Z.h, i < j →
      0 ≤ (InflatedContSet.nominal Zs).G i 0 * (InflatedContSet.nominal Zs).G j 1
        - (InflatedContSet.nominal Zs).G i 1 * (InflatedContSet.nominal Zs).G j 0 :=
    fun i j hij => by
    have h := hsorted i j
    rcases h with h | h
    · exact absurd hij (by simpa using h)
    · -- the rounded-down cross product is below the exact one
      have a1 := subDown_le_sub (mulDown (Zs.G i 0) (Zs.G j 1)) (mulUp (Zs.G i 1) (Zs.G j 0))
      have a2 := mulDown_le_mul (Zs.G i 0) (Zs.G j 1)
      have a3 := mul_le_mulUp (Zs.G i 1) (Zs.G j 0)
      have a4 := toReal_le_of_le h
      rw [toReal_zero] at a4
      show 0 ≤ toReal (Zs.G i 0) * toReal (Zs.G j 1) - toReal (Zs.G i 1) * toReal (Zs.G j 0)
      have a5 : toReal (cross (Zs.G i) (Zs.G j)) ≤ _ := a1
      linarith
  -- the nominal sorted zonotope lies in the hull of its exact walk
  have hreal := Real.Zonotope.construct_subset_walk (InflatedContSet.nominal Zs) hH1 hH2
  rw [← Real.VPolytope.construct_eq_convexHull
    (Real.VPolytope.mk _ (InflatedContSet.nominal Zs).walk)] at hreal
  -- an exact corner lies between the two roundings of its signed sum
  have hcorner : ∀ (σ : Fin Zs.h → Bool) (i : Fin 2), toReal (Zs.cornerLo
      ((signEquiv Zs.h).symm σ) i) ≤ (InflatedContSet.nominal Zs).corner σ i ∧
      (InflatedContSet.nominal Zs).corner σ i ≤ toReal (Zs.cornerHi ((signEquiv Zs.h).symm σ) i) :=
    fun σ i => by
    have hsig : ∀ j, toReal (Zs.signed σ i j)
        = (if σ j then (1 : ℝ) else -1) * toReal (Zs.G j i) := fun j => by
      by_cases hj : σ j = true
      · simp [Zonotope.signed, hj]
      · simp [Zonotope.signed, hj, toReal_neg]
    have hval : (InflatedContSet.nominal Zs).corner σ i
        = toReal (Zs.c i) + ∑ j, toReal (Zs.signed σ i j) := by
      show toReal (Zs.c i) + (∑ j, (if σ j then (1 : ℝ) else -1) •
        (fun i => toReal (Zs.G j i) : Vec ℝ 2)) i = _
      rw [Finset.sum_apply]
      exact congrArg _ (Finset.sum_congr rfl fun j _ => (hsig j).symm)
    -- the rounded sums bracket the exact sum
    rw [hval]
    simp only [Zonotope.cornerLo, Zonotope.cornerHi, Equiv.apply_symm_apply]
    exact ⟨le_trans (addDown_le_add _ _) (add_le_add le_rfl (sumDown_le_sum _)),
      le_trans (add_le_add le_rfl (sum_le_sumUp _)) (add_le_addUp _ _)⟩
  -- the walk and the stored vertices, block by block
  have hw1 : ∀ k : Fin (Zs.h + 1), (InflatedContSet.nominal Zs).walk (Fin.castAdd (Zs.h + 1) k)
      = (InflatedContSet.nominal Zs).corner fun j => decide (j.val < k.val) :=
    fun k => Fin.append_left _ _ k
  have hw2 : ∀ k : Fin (Zs.h + 1), (InflatedContSet.nominal Zs).walk (Fin.natAdd (Zs.h + 1) k)
      = (InflatedContSet.nominal Zs).corner fun j => !decide (j.val < k.val) :=
    fun k => Fin.append_right _ _ k
  have hl1 : ∀ k : Fin (Z.h + 1), lo (Fin.castAdd (Z.h + 1) k) = Zs.cornerLo
      ((signEquiv Zs.h).symm fun j => decide (j.val < k.val)) := fun k => Fin.append_left _ _ k
  have hl2 : ∀ k : Fin (Z.h + 1), lo (Fin.natAdd (Z.h + 1) k) = Zs.cornerLo
      ((signEquiv Zs.h).symm fun j => !decide (j.val < k.val)) := fun k => Fin.append_right _ _ k
  have hh1 : ∀ k : Fin (Z.h + 1), hi (Fin.castAdd (Z.h + 1) k) = Zs.cornerHi
      ((signEquiv Zs.h).symm fun j => decide (j.val < k.val)) := fun k => Fin.append_left _ _ k
  have hh2 : ∀ k : Fin (Z.h + 1), hi (Fin.natAdd (Z.h + 1) k) = Zs.cornerHi
      ((signEquiv Zs.h).symm fun j => !decide (j.val < k.val)) := fun k => Fin.append_right _ _ k
  -- each exact walk corner lies between its two stored roundings
  have hbnd : ∀ (m : Fin ((Z.h + 1) + (Z.h + 1))) (i : Fin 2), toReal (lo m i)
      ≤ (InflatedContSet.nominal Zs).walk m i ∧ (InflatedContSet.nominal Zs).walk m i
      ≤ toReal (hi m i) := fun m i => by
    -- the first block's index is a `castAdd`, the second's a `natAdd`
    refine Fin.addCases (fun k => ?_) (fun k => ?_) m
    · have h := hcorner (fun j => decide (j.val < k.val)) i
      exact ⟨le_of_eq_of_le (congrArg (fun v : Vec 𝕋 2 => toReal (v i)) (hl1 k))
          (le_of_le_of_eq h.1 (congrArg (fun v : Vec ℝ 2 => v i) (hw1 k)).symm),
        le_of_eq_of_le (congrArg (fun v : Vec ℝ 2 => v i) (hw1 k))
          (le_of_le_of_eq h.2 (congrArg (fun v : Vec 𝕋 2 => toReal (v i)) (hh1 k)).symm)⟩
    · have h := hcorner (fun j => !decide (j.val < k.val)) i
      exact ⟨le_of_eq_of_le (congrArg (fun v : Vec 𝕋 2 => toReal (v i)) (hl2 k))
          (le_of_le_of_eq h.1 (congrArg (fun v : Vec ℝ 2 => v i) (hw2 k)).symm),
        le_of_eq_of_le (congrArg (fun v : Vec ℝ 2 => v i) (hw2 k))
          (le_of_le_of_eq h.2 (congrArg (fun v : Vec 𝕋 2 => toReal (v i)) (hh2 k)).symm)⟩
  -- so the exact walk's hull is in the stored vertices plus the column gap
  have hstep : (Real.VPolytope.mk _ (InflatedContSet.nominal Zs).walk).construct
      ⊆ (Real.VPolytope.mk _ fun m i => toReal (lo m i)).construct
        + (VPolytope.columnGap lo hi).construct :=
    Real.VPolytope.construct_subset_add _ _ (Real.Interval.convex_construct _) fun m =>
      VPolytope.mem_columnGap (p := (InflatedContSet.nominal Zs).walk m) (l := m) (hbnd m)
  -- add the zonotope's own box
  intro x hx
  obtain ⟨p, hp, e, he, rfl⟩ := hS hx
  have he' : e ∈ Z.I_error.construct := by
    have h : e ∈ Zs.I_error.construct := he
    rw [hEs] at h; exact h
  obtain ⟨v, hv, g, hg, hvg⟩ := hstep (hreal hp)
  refine ⟨v, hv, g + e, ?_, ?_⟩
  · exact Interval.plus_outer _ _ ⟨g, hg, e, he', rfl⟩
  · have hvg' : v + g = p := hvg
    show v + (g + e) = p + e
    rw [← add_assoc, hvg']

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
