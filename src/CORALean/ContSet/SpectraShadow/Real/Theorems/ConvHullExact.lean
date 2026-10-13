import CORALean.ContSet.SpectraShadow.Real.Operations.ConvHull
import CORALean.ContSet.SpectraShadow.Real.Theorems.SingletonOneConstruct
import CORALean.ContSet.SpectraShadow.Real.Theorems.HyperplaneOneConstruct
import CORALean.ContSet.SpectraShadow.Real.Theorems.ConeConstruct
import CORALean.ContSet.SpectraShadow.Real.Theorems.CartProdExact
import CORALean.ContSet.SpectraShadow.Real.Theorems.InterExact
import CORALean.ContSet.SpectraShadow.Real.Theorems.PlusExact
import CORALean.ContSet.SpectraShadow.Real.Theorems.ProjectExact
import CORALean.ContSet.SpectraShadow.Real.Theorems.Convex
import Mathlib.Analysis.Convex.Hull

/-!
# `SpectraShadow.convHull_` is exactly the convex hull of the union

The cones are `s x` for `s > 0` and the origin (`cone_construct`), so a point of their sum at
height `1` is `s₁ x₁ + s₂ x₂` with `s₁ + s₂ = 1`, `sᵢ > 0`, or one of the two summands is the
origin and the point is the other shadow's. Every such point is a convex combination of points
of the union; conversely the union is inside, and the result is convex (a shadow), so it holds
the hull. Exact, with no closure and no emptiness case: the hull of `∅` and `S` is `S`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

open Matrix CORALean Pointwise

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.convHull_exact (S₁ S₂ : SpectraShadow (Vec ℝ n)) :
    (S₁.convHull_ S₂).construct = convexHull ℝ (S₁.construct ∪ S₂.construct) := by -- --- PROOF ---
  set app : Vec ℝ n → Vec ℝ (n + 1) := fun x => Fin.append x (fun _ : Fin 1 => (1 : ℝ)) with happ
  -- the cone of a shadow at height one
  have hcone : ∀ S : SpectraShadow (Vec ℝ n), (S.cartProd SpectraShadow.singletonOne).cone.construct
      = {z : Vec ℝ (n + 1) | z = 0 ∨ ∃ s : ℝ, 0 < s ∧ ∃ x ∈ S.construct, z = s • app x} := by
    intro S
    rw [SpectraShadow.cone_construct (Nat.succ_pos n), ← SpectraShadow.cartProd_exact,
      SpectraShadow.singletonOne_construct]
    ext z
    simp only [Set.mem_setOf_eq, Set.prod_singleton, Set.image_image, Set.mem_image]
    constructor <;> rintro (h | ⟨s, hs, x, hx, rfl⟩)
    · exact Or.inl h
    · obtain ⟨x, hx, rfl⟩ := hx
      exact Or.inr ⟨s, hs, x, hx, rfl⟩
    · exact Or.inl h
    · exact Or.inr ⟨s, hs, _, ⟨x, hx, rfl⟩, rfl⟩
  -- the result is the projection of the sum of the two cones, cut at height one
  have key : (S₁.convHull_ S₂).construct
      = (fun w k => w (Fin.castAdd 1 k)) ''
        (({z : Vec ℝ (n + 1) | z = 0 ∨ ∃ s : ℝ, 0 < s ∧ ∃ x ∈ S₁.construct, z = s • app x}
          + {z : Vec ℝ (n + 1) | z = 0 ∨ ∃ s : ℝ, 0 < s ∧ ∃ x ∈ S₂.construct, z = s • app x})
          ∩ {w : Vec ℝ (n + 1) | w (Fin.natAdd n 0) = 1}) := by
    unfold SpectraShadow.convHull_
    simp only []
    rw [← SpectraShadow.project_exact, ← SpectraShadow.inter_exact, ← SpectraShadow.plus_exact,
      hcone, hcone, SpectraShadow.hyperplaneOne_construct]
  -- the coordinates of `s • app x`: the last is `s`, the first `n` are `s x`
  have hlast : ∀ (s : ℝ) (x : Vec ℝ n), (s • app x) (Fin.natAdd n 0) = s := fun s x => by
    simp [happ]
  have hinit : ∀ (s : ℝ) (x : Vec ℝ n) (k : Fin n), (s • app x) (Fin.castAdd 1 k) = s * x k :=
    fun s x k => by simp [happ]
  rw [key]
  apply Set.eq_of_subset_of_subset
  -- inside the hull: a point of the sum at height one is a convex combination of the two sets'
  · rintro _ ⟨w, ⟨⟨z₁, hz₁, z₂, hz₂, rfl⟩, hw⟩, rfl⟩
    rcases hz₁ with rfl | ⟨s₁, hs₁, x₁, hx₁, rfl⟩ <;>
      rcases hz₂ with rfl | ⟨s₂, hs₂, x₂, hx₂, rfl⟩
    · simp at hw
    · simp only [Set.mem_setOf_eq, zero_add, hlast] at hw
      subst hw
      refine subset_convexHull ℝ _ (Or.inr ?_)
      convert hx₂ using 1
      funext k
      simp [happ]
    · simp only [Set.mem_setOf_eq, add_zero, hlast] at hw
      subst hw
      refine subset_convexHull ℝ _ (Or.inl ?_)
      convert hx₁ using 1
      funext k
      simp [happ]
    -- both summands off the apex: heights `s₁ + s₂ = 1`, a convex combination
    · simp only [Set.mem_setOf_eq, Pi.add_apply, hlast] at hw
      have := (convex_convexHull ℝ (S₁.construct ∪ S₂.construct))
        (subset_convexHull ℝ _ (Or.inl hx₁)) (subset_convexHull ℝ _ (Or.inr hx₂)) hs₁.le hs₂.le hw
      convert this using 1
      funext k
      simp [hinit]
  -- the hull is inside, as both sets are and the result is convex
  · rw [← key]
    refine convexHull_min ?_ (SpectraShadow.convex_construct _)
    rw [key]
    have hx1 : ∀ x : Vec ℝ n, app x (Fin.natAdd n 0) = 1 := fun x => by simp [happ]
    have hx2 : ∀ x : Vec ℝ n, (fun k => app x (Fin.castAdd 1 k)) = x := fun x => by
      funext k; simp [happ]
    rintro x (hx | hx)
    · exact ⟨app x, ⟨⟨1 • app x, Or.inr ⟨1, one_pos, x, hx, rfl⟩, 0, Or.inl rfl, by simp⟩,
        hx1 x⟩, hx2 x⟩
    · exact ⟨app x, ⟨⟨0, Or.inl rfl, 1 • app x, Or.inr ⟨1, one_pos, x, hx, rfl⟩, by simp⟩,
        hx1 x⟩, hx2 x⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
