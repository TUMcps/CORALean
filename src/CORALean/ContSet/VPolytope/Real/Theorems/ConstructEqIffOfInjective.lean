module

public import CORALean.ContSet.VPolytope.Real.Theorems.ConvexHull
public import CORALean.ContSet.VPolytope.Real.Theorems.Basic
public import CORALean.Global.DropIdx
public import Mathlib.Analysis.Convex.KreinMilman
public import Mathlib.Analysis.Convex.Join
public import Mathlib.Tactic.Module

@[expose] public section

/-!
# Set equality of V-polytopes, by their points

[1, Eq. 7]: two V-polytopes are equal exactly when every point of each is a point of the other
or redundant in its own list in the sense of [1, Eq. 2]. That needs the points of each list to
be distinct: a point listed twice is redundant by its copy, so `⟨[a a]⟩` and `⟨[b b]⟩` pass the
test for any `a ≠ b` (`construct_eq_iff_counterexample`). With distinct points a non-redundant
one is an extreme point, which the other list must contain; conversely every extreme point then
lies in the other polytope, and Krein–Milman gives the rest.

## Inputs
* `P₁` – first polytope
* `P₂` – second polytope

## Hypotheses
* `h₁` – vertices of `P₁` distinct
* `h₂` – vertices of `P₂` distinct

## Conclusion
* the sets are equal iff every vertex is shared or redundant

## References

* [1] [M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral
      Operations in CORA 2024". Proceedings of the 11th Int. Workshop on Applied Verification for
      Continuous and Hybrid Systems,
      2024.](../../../../../../references/2024/wetzlinger-arch-polyhedral-operations.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A point outside the hull of the others is an extreme point of the hull of all. -/
private theorem aux_mem_extremePoints {E : Type} [AddCommGroup E] [Module ℝ E] {x : E} {t : Set E}
    (hx : x ∉ convexHull ℝ t) : -- --- CONCL ---
    x ∈ (convexHull ℝ (insert x t)).extremePoints ℝ := by -- --- PROOF ---
  rcases t.eq_empty_or_nonempty with rfl | ht
  · rw [insert_empty_eq, convexHull_singleton, extremePoints_singleton]
    exact Set.mem_singleton x
  rw [convexHull_insert ht, mem_extremePoints]
  refine ⟨mem_convexJoin.mpr ⟨x, rfl, ht.some, subset_convexHull ℝ t ht.some_mem,
    left_mem_segment ℝ _ _⟩, fun x₁ hx₁ x₂ hx₂ hseg => ?_⟩
  rw [convexJoin_singleton_left, Set.mem_iUnion₂] at hx₁ hx₂
  obtain ⟨p, hp, a₁, α, ha₁, hα, h1, rfl⟩ := hx₁
  obtain ⟨q, hq, a₂, β, ha₂, hβ, h2, rfl⟩ := hx₂
  obtain ⟨a, b, ha, hb, hab, hx12⟩ := hseg
  obtain rfl : a₁ = 1 - α := by linarith
  obtain rfl : a₂ = 1 - β := by linarith
  obtain rfl : b = 1 - a := by linarith
  -- `c x = aα p + bβ q` with `c = aα + bβ`
  have hcomb : (a * α + (1 - a) * β) • x = (a * α) • p + ((1 - a) * β) • q := by
    linear_combination (norm := module) -hx12
  have haα := mul_nonneg ha.le hα
  have hbβ := mul_nonneg hb.le hβ
  rcases (add_nonneg haα hbβ).eq_or_lt with hc0 | hcpos
  -- `c = 0`: neither endpoint leaves `x`
  · have hα0 : α = 0 := (mul_eq_zero.mp (by linarith : a * α = 0)).resolve_left ha.ne'
    have hβ0 : β = 0 := (mul_eq_zero.mp (by linarith : (1 - a) * β = 0)).resolve_left hb.ne'
    subst hα0 hβ0
    simp
  -- `c > 0`: `x` would be a convex combination of `p` and `q`
  · exfalso
    apply hx
    set c := a * α + (1 - a) * β with hc
    have hxe : x = (a * α / c) • p + ((1 - a) * β / c) • q := by
      have := congrArg (fun v => c⁻¹ • v) hcomb
      simp only [smul_smul, inv_mul_cancel₀ hcpos.ne', one_smul, smul_add] at this
      rw [this, div_eq_inv_mul, div_eq_inv_mul]
    rw [hxe]
    exact convex_convexHull ℝ t hp hq (div_nonneg haα hcpos.le) (div_nonneg hbβ hcpos.le)
      (by rw [← add_div, ← hc, div_self hcpos.ne'])

/-- A dropped index is never the one dropped. -/
private theorem aux_dropIdx_ne {k : ℕ} (j : Fin k) (i : Fin (k - 1)) : dropIdx j i ≠ j := fun h =>
    by
  have := insertIdx_dropIdx j true (fun _ => false) i
  rw [h, insertIdx_self] at this
  exact Bool.noConfusion this

/-- The point `j` and the others make up the whole list. -/
private theorem aux_insert_range {α : Type} {k : ℕ} (V : Fin k → α) (j : Fin k) : -- --- CONCL ---
    insert (V j) (Set.range fun i => V (dropIdx j i)) = Set.range V := by -- --- PROOF ---
  ext y
  constructor
  · rintro (rfl | ⟨i, rfl⟩)
    · exact ⟨j, rfl⟩
    · exact ⟨dropIdx j i, rfl⟩
  · rintro ⟨l, rfl⟩
    revert l
    exact (forall_dropIdx_iff j (P := fun l => V l ∈ insert (V j)
      (Set.range fun i => V (dropIdx j i)))).mpr ⟨Or.inl rfl, fun i => Or.inr ⟨i, rfl⟩⟩

/-- With distinct points, a point is non-redundant exactly when it is extreme. -/
private theorem aux_notMem_iff_extreme (P : VPolytope (Vec ℝ n)) (hP : Function.Injective P.V)
    (j : Fin P.k) : -- --- CONCL ---
    P.V j ∉ (⟨P.k - 1, fun i => P.V (dropIdx j i)⟩ : VPolytope (Vec ℝ n)).construct ↔
      P.V j ∈ P.construct.extremePoints ℝ := by -- --- PROOF ---
  rw [VPolytope.construct_eq_convexHull, VPolytope.construct_eq_convexHull]
  constructor
  · intro h
    have := aux_mem_extremePoints h
    rwa [aux_insert_range] at this
  · intro h hmem
    rw [(convex_convexHull ℝ _).mem_extremePoints_iff_mem_sdiff_convexHull_sdiff] at h
    -- the other points lie in the hull and differ from `V j`
    refine h.2 (convexHull_mono ?_ hmem)
    rintro _ ⟨i, rfl⟩
    exact ⟨subset_convexHull ℝ _ ⟨_, rfl⟩, fun he => aux_dropIdx_ne j i (hP he)⟩

/-- Every extreme point of `P₁` in `P₂` puts `P₁` in `P₂`. -/
private theorem aux_subset_of_extreme (P₁ P₂ : VPolytope (Vec ℝ n))
    (h : P₁.construct.extremePoints ℝ ⊆ P₂.construct) : P₁.construct ⊆ P₂.construct := by
  rw [← closure_convexHull_extremePoints P₁.isCompact_construct P₁.convex_construct]
  exact closure_minimal (convexHull_min h P₂.convex_construct) P₂.isClosed_construct


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.construct_eq_iff_of_injective (P₁ P₂ : VPolytope (Vec ℝ n))
    (h₁ : Function.Injective P₁.V) (h₂ : Function.Injective P₂.V) : -- --- CONCL ---
    P₁.construct = P₂.construct ↔
      (∀ j, (∃ k, P₁.V j = P₂.V k) ∨
          P₁.V j ∈ (⟨P₁.k - 1, fun i => P₁.V (dropIdx j i)⟩ : VPolytope (Vec ℝ n)).construct) ∧
        ∀ k, (∃ j, P₂.V k = P₁.V j) ∨
          P₂.V k ∈ (⟨P₂.k - 1, fun i => P₂.V (dropIdx k i)⟩ :
            VPolytope (Vec ℝ n)).construct := by -- --- PROOF ---
  -- an extreme point of one hull lies among the points of the other
  have hext : ∀ Q₁ Q₂ : VPolytope (Vec ℝ n), Q₁.construct = Q₂.construct →
      ∀ x ∈ Q₁.construct.extremePoints ℝ, ∃ k, x = Q₂.V k := fun Q₁ Q₂ he x hx => by
    rw [he, Q₂.construct_eq_convexHull] at hx
    obtain ⟨k, hk⟩ := extremePoints_convexHull_subset hx
    exact ⟨k, hk.symm⟩
  -- the test, on one side, puts every extreme point into the other polytope
  have hsub : ∀ Q₁ Q₂ : VPolytope (Vec ℝ n), Function.Injective Q₁.V →
      (∀ j, (∃ k, Q₁.V j = Q₂.V k) ∨
        Q₁.V j ∈ (⟨Q₁.k - 1, fun i => Q₁.V (dropIdx j i)⟩ : VPolytope (Vec ℝ n)).construct) →
      Q₁.construct ⊆ Q₂.construct := fun Q₁ Q₂ hQ ht => by
    refine aux_subset_of_extreme Q₁ Q₂ fun x hx => ?_
    have hx' := hx
    rw [Q₁.construct_eq_convexHull] at hx'
    obtain ⟨j, rfl⟩ := extremePoints_convexHull_subset hx'
    rcases ht j with ⟨k, hk⟩ | hred
    · exact hk ▸ Q₂.vertex_mem k
    · exact absurd hred ((aux_notMem_iff_extreme Q₁ hQ j).mpr hx)
  -- equal polytopes: a non-redundant point is extreme, hence a point of the other list
  constructor
  · intro he
    refine ⟨fun j => ?_, fun k => ?_⟩
    · by_cases hred : P₁.V j ∈ (⟨P₁.k - 1, fun i => P₁.V (dropIdx j i)⟩ :
          VPolytope (Vec ℝ n)).construct
      · exact Or.inr hred
      · exact Or.inl (hext P₁ P₂ he _ ((aux_notMem_iff_extreme P₁ h₁ j).mp hred))
    · by_cases hred : P₂.V k ∈ (⟨P₂.k - 1, fun i => P₂.V (dropIdx k i)⟩ :
          VPolytope (Vec ℝ n)).construct
      · exact Or.inr hred
      · exact Or.inl (hext P₂ P₁ he.symm _ ((aux_notMem_iff_extreme P₂ h₂ k).mp hred))
  · rintro ⟨ht₁, ht₂⟩
    exact Set.Subset.antisymm (hsub P₁ P₂ h₁ ht₁) (hsub P₂ P₁ h₂ ht₂)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
