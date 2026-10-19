module

public import CORALean.ContSet.ConPolyZono.Real.Operations.MinkDiff
public import CORALean.ContSet.ConPolyZono.Real.Theorems.IntersectionExact
public import CORALean.ContSet.ConPolyZono.Real.Theorems.PlusExact
public import CORALean.ContSet.ConPolyZono.Real.Theorems.OfPointMemIff
public import CORALean.ContSet.ConPolyZono.Real.Theorems.DependentExact

@[expose] public section

/-!
# What `ConPolyZono.minkDiff` computes

A point is in the result exactly when it lies in the minuend at every vertex of the subtrahend
reached by a choice of signs: `x ∈ P ⊖ Z` is tested at `x + c + Σⱼ ±gⱼ`, the `2ʰ` corner points of
the zonotope (with its center), and nowhere else. Each step `(P + g) ∩ (P - g)` asks `x - g` and
`x + g` to lie in the set so far, and the steps compose over the generators.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open scoped Pointwise

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- One step: `x` is in `(P + g) ∩ (P - g)` iff both `x - g` and `x + g` are in `P`. -/
theorem ConPolyZono.aux_mem_minkDiffStep (X : ConPolyZono (Vec ℝ n)) (g x : Vec ℝ n) :
    x ∈ ((X.plus (ConPolyZono.ofPoint g)).intersection
        (X.plus (ConPolyZono.ofPoint (-g)))).construct
      ↔ x - g ∈ X.construct ∧ x + g ∈ X.construct := by -- --- PROOF ---
  rw [← ConPolyZono.intersection_exact, ← ConPolyZono.plus_exact, ← ConPolyZono.plus_exact]
  -- membership in a sum with a point is a shift
  have hshift : ∀ v : Vec ℝ n, x ∈ X.construct + (ConPolyZono.ofPoint v).construct
      ↔ x - v ∈ X.construct := fun v => by
    constructor
    · rintro ⟨y, hy, z, hz, rfl⟩
      rw [(ConPolyZono.mem_ofPoint_iff v z).mp hz, add_sub_cancel_right]
      exact hy
    · intro h
      exact ⟨x - v, h, v, ConPolyZono.mem_ofPoint v, sub_add_cancel x v⟩
  show (x ∈ X.construct + (ConPolyZono.ofPoint g).construct
    ∧ x ∈ X.construct + (ConPolyZono.ofPoint (-g)).construct) ↔ _
  rw [hshift, hshift, sub_neg_eq_add]

/-- The fold over `m` generators tests the minuend at every corner `x + Σⱼ ±Gⱼ`. -/
theorem ConPolyZono.aux_foldl_minkDiff {m : ℕ} (G : Fin m → Vec ℝ n)
    (X : ConPolyZono (Vec ℝ n)) : -- --- CONCL ---
    (Fin.foldl m (fun cPZ i => (cPZ.plus (ConPolyZono.ofPoint (G i))).intersection
        (cPZ.plus (ConPolyZono.ofPoint (-G i)))) X).construct
      = {x | ∀ s : Fin m → Bool,
          x + ∑ j, (if s j then G j else -G j) ∈ X.construct} := by -- --- PROOF ---
  -- by induction on the number of generators, peeling off the first
  induction m generalizing X with
  | zero =>
    ext x
    simp [Fin.foldl_zero]
  | succ m ih =>
    rw [Fin.foldl_succ, ih (fun j => G j.succ)]
    ext x
    -- split the signs into the first generator's sign `b` and the signs `s'` of the others
    have hR : (∀ s : Fin (m + 1) → Bool, x + ∑ j, (if s j then G j else -G j) ∈ X.construct)
        ↔ ∀ (b : Bool) (s' : Fin m → Bool), x + ((if b then G 0 else -G 0)
            + ∑ j, (if s' j then G j.succ else -G j.succ)) ∈ X.construct := by
      rw [Fin.forall_fin_succ_pi]
      simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    show (∀ s' : Fin m → Bool, x + ∑ j, (if s' j then G j.succ else -G j.succ) ∈ _) ↔
      ∀ s : Fin (m + 1) → Bool, x + ∑ j, (if s j then G j else -G j) ∈ X.construct
    rw [hR]
    refine Iff.trans (forall_congr' fun s' => ConPolyZono.aux_mem_minkDiffStep X (G 0) _) ?_
    -- the two memberships of the step are the two signs of the first generator
    constructor
    · intro h b s'
      cases b
      · rw [show x + ((if false = true then G 0 else -G 0) + ∑ j, (if s' j then G j.succ
          else -G j.succ)) = x + ∑ j, (if s' j then G j.succ else -G j.succ) - G 0 by simp; abel]
        exact (h s').1
      · rw [show x + ((if true = true then G 0 else -G 0) + ∑ j, (if s' j then G j.succ
          else -G j.succ)) = x + ∑ j, (if s' j then G j.succ else -G j.succ) + G 0 by simp; abel]
        exact (h s').2
    · intro h s'
      refine ⟨?_, ?_⟩
      · have := h false s'
        rwa [show x + ((if false = true then G 0 else -G 0) + ∑ j, (if s' j then G j.succ
          else -G j.succ)) = x + ∑ j, (if s' j then G j.succ else -G j.succ) - G 0 by
            simp; abel] at this
      · have := h true s'
        rwa [show x + ((if true = true then G 0 else -G 0) + ∑ j, (if s' j then G j.succ
          else -G j.succ)) = x + ∑ j, (if s' j then G j.succ else -G j.succ) + G 0 by
            simp; abel] at this


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.minkDiff_construct (cPZ₁ : ConPolyZono (Vec ℝ n)) (Z : Zonotope (Vec ℝ n)) :
    (cPZ₁.minkDiff Z).construct
      = {x | ∀ s : Fin Z.h → Bool,
          x + (Z.c + ∑ j, (if s j then Z.G j else -Z.G j)) ∈ cPZ₁.construct} := by -- --- PROOF ---
  unfold ConPolyZono.minkDiff
  simp only []
  rw [ConPolyZono.aux_foldl_minkDiff]
  ext x
  simp only [Set.mem_setOf_eq]
  -- the center is one more shift, undone by `plus (ofPoint (-c))` and `dependent_exact`
  have hshift : ∀ y : Vec ℝ n, y ∈ (cPZ₁.dependent.plus (ConPolyZono.ofPoint (-Z.c))).construct
      ↔ y + Z.c ∈ cPZ₁.construct := fun y => by
    rw [← ConPolyZono.plus_exact]
    constructor
    · rintro ⟨u, hu, v, hv, rfl⟩
      rw [(ConPolyZono.mem_ofPoint_iff _ v).mp hv, neg_add_cancel_right]
      exact (ConPolyZono.dependent_exact cPZ₁) ▸ hu
    · intro h
      exact ⟨y + Z.c, (ConPolyZono.dependent_exact cPZ₁) ▸ h, -Z.c, ConPolyZono.mem_ofPoint _,
        add_neg_cancel_right y Z.c⟩
  refine forall_congr' fun s => ?_
  rw [hshift, add_assoc, add_comm _ Z.c]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
