module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.ContSet.Zonotope.Real.Theorems.Convex
public import CORALean.ContSet.VPolytope.Real.VPolytope
public import CORALean.ContSet.VPolytope.Real.Theorems.ConvexHull
public import CORALean.Global.Corners
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_VPolytope

@[expose] public section

/-!
# A zonotope as its corners

`Zonotope.vPolytope_contains`: its `vPolytope` contains it.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.vPolytope_contains (Z : Zonotope α) :
    Z.construct ⊆ Z.vPolytope.construct := by -- --- PROOF ---
  rintro _ ⟨β, hβ, rfl⟩
  -- how far from `-1` towards `1` each coefficient sits
  set t : Fin Z.h → ℝ := fun j => (β j + 1) / 2 with htdef
  have ht0 : ∀ j, 0 ≤ t j := fun j => by
    have h := abs_le.mp (hβ j); rw [htdef]; simp only; linarith [h.1]
  have ht1 : ∀ j, t j ≤ 1 := fun j => by
    have h := abs_le.mp (hβ j); rw [htdef]; simp only; linarith [h.2]
  have hone : (∑ σ : Fin Z.h → Bool, ∏ j, (if σ j then t j else 1 - t j)) = 1 := by
    rw [sum_prod_bool]; simp
  have hcoef : ∀ j, (∑ σ : Fin Z.h → Bool,
      (∏ k, (if σ k then t k else 1 - t k)) * (if σ j then (1:ℝ) else -1)) = β j := by
    intro j
    rw [sum_prod_bool_mul t (fun _ => 1) (fun _ => -1) j, htdef]
    ring
  -- one corner's contribution, split into centre and generators
  have hR : ∀ σ : Fin Z.h → Bool,
      (∏ j, (if σ j then t j else 1 - t j)) • Z.corner σ
        = (∏ j, (if σ j then t j else 1 - t j)) • Z.c
          + ∑ j, ((∏ k, (if σ k then t k else 1 - t k))
              * (if σ j then (1:ℝ) else -1)) • Z.G j := by
    intro σ
    rw [Zonotope.corner, smul_add, Finset.smul_sum]
    exact congrArg _ (Finset.sum_congr rfl fun j _ => smul_smul _ _ _)
  -- a corner's convex weight is the product of the per-generator ones
  refine ⟨fun l => ∏ j, (if signEquiv Z.h l j then t j else 1 - t j), fun l => ?_, ?_, ?_⟩
  · exact Finset.prod_nonneg fun j _ => by
      cases signEquiv Z.h l j <;> simp <;> linarith [ht0 j, ht1 j]
  · show ∑ l : Fin (2 ^ Z.h), (∏ j, (if signEquiv Z.h l j then t j else 1 - t j)) = 1
    rw [Fintype.sum_equiv (signEquiv Z.h)
        (fun l => ∏ j, (if signEquiv Z.h l j then t j else 1 - t j))
        (fun σ => ∏ j, (if σ j then t j else 1 - t j)) fun _ => rfl]
    exact hone
  · show Z.c + ∑ j, β j • Z.G j
        = ∑ l : Fin (2 ^ Z.h), (∏ j, (if signEquiv Z.h l j then t j else 1 - t j)) •
            Z.corner (signEquiv Z.h l)
    rw [Fintype.sum_equiv (signEquiv Z.h)
      (fun l => (∏ j, (if signEquiv Z.h l j then t j else 1 - t j)) • Z.corner (signEquiv Z.h l))
      (fun σ : Fin Z.h → Bool => (∏ j, (if σ j then t j else 1 - t j)) • Z.corner σ) fun _ => rfl,
      Finset.sum_congr rfl fun σ (_ : σ ∈ (Finset.univ : Finset (Fin Z.h → Bool))) => hR σ,
      Finset.sum_add_distrib, ← Finset.sum_smul, hone, one_smul, Finset.sum_comm]
    refine congrArg (fun y => Z.c + y) (Finset.sum_congr rfl fun j _ => ?_)
    rw [← Finset.sum_smul, hcoef j]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
