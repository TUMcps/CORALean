module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.ContSet.Zonotope.Real.Theorems.Convex
public import CORALean.ContSet.VPolytope.Real.VPolytope
public import CORALean.ContSet.VPolytope.Real.Theorems.ConvexHull
public import CORALean.Global.Corners
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

/-!
# A zonotope as its corners

CORA's `polytope(zonotope)`: `2ʰ` vertices, one per choice of sign per
generator. Exponential in the generator count, which is what makes it the
conversion CORA avoids — but it loses nothing, every point of the zonotope being
a convex combination of the sign corners, and every such combination lying back
in the zonotope since it is convex — `vPolytope_exact` is [1, Eq. 9], read at
any generator's larger (non-minimal) corner set, `Zonotope (Mat ℝ n n)` being
[1, Eq. 8]'s matrix zonotope.

The same weights as a box's corners, and for the same reason: a box *is* the
zonotope with axis-aligned generators. A coefficient `βⱼ ∈ [-1, 1]` sits a
fraction `(βⱼ + 1)/2` of the way from `-1` to `1`, a corner's weight is the
product of those fractions and their complements, and every generator's weight
sums back to its own coefficient while the rest sum away.

## References

* [1] M. Althoff, B. H. Krogh and O. Stursberg. "Analyzing Reachability of Linear
      Dynamic Systems with Parametric Uncertainties". In A. Rauh and E. Auer (eds.),
      Modeling, Design, and Simulation of Systems with Uncertainties, Springer, 2011.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

/-- The vertex a choice of sign per generator picks out. -/
def Zonotope.corner (Z : Zonotope α) (σ : Fin Z.h → Bool) : α :=
  Z.c + ∑ j, (if σ j then (1:ℝ) else -1) • Z.G j

noncomputable def Zonotope.vPolytope (Z : Zonotope α) : VPolytope α where
  k := 2 ^ Z.h
  V := fun l => Z.corner (signEquiv Z.h l)


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

-- back: each listed vertex is a corner, and every corner lies in the zonotope
theorem Zonotope.contains_vPolytope (Z : Zonotope α) :
    Z.vPolytope.construct ⊆ Z.construct := by -- --- PROOF ---
  rw [VPolytope.construct_eq_convexHull]
  refine convexHull_min ?_ Z.convex_construct
  rintro _ ⟨l, rfl⟩
  exact ⟨fun j => if signEquiv Z.h l j then (1 : ℝ) else -1,
    fun j => by dsimp only; split_ifs <;> norm_num, rfl⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.vPolytope_exact (Z : Zonotope α) :
    Z.vPolytope.construct = Z.construct :=
  Set.Subset.antisymm Z.contains_vPolytope Z.vPolytope_contains

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
