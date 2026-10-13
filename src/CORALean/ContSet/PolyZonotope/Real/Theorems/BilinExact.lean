import CORALean.ContSet.PolyZonotope.Real.Theorems.BilinPoint

/-!
# `bilin` is exactly the pairing over shared factors

What exactness can mean here, and what it cannot: `construct (bilin f pZ₁ pZ₂)` is
not `f '' (construct pZ₁ ×ˢ construct pZ₂)`. Both sets are functions of one shared
factor vector, so `f` at their points ranges over far fewer points than `f` over
the two sets independently. The claim is about the evaluation map — the result is
exactly the image of the admissible factors under `a ↦ f (point pZ₁ a) (point pZ₂ a)`,
with `pZ₂` read at the same factors through `Fin.cast`.

`bilin_point` gives that fact directly, `bilin`'s own point unfolding to the sum
this file reads it back through.

The independent blocks are not hypothesised away: `point` ignores them, so they
take no part on either side.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open PolyZonotope

variable {α β γ : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]
  [AddCommGroup γ] [Module ℝ γ]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.bilin_exact (f : α →ₗ[ℝ] β →ₗ[ℝ] γ) (pZ₁ : PolyZonotope α)
    (pZ₂ : PolyZonotope β) (hp : pZ₁.p = pZ₂.p) :
    (fun a : Fin pZ₁.p → ℝ => f (pZ₁.point a) (pZ₂.point fun k => a (Fin.cast hp.symm k)))
        '' {a | ∀ k, |a k| ≤ 1}
      = (pZ₁.bilin f pZ₂ hp).construct := by -- --- PROOF ---
  -- the result has an empty independent block, so a point of it is the sum alone
  have hpt : ∀ (a : Fin pZ₁.p → ℝ) (b : Fin 0 → ℝ),
      f (pZ₁.point a) (pZ₂.point fun k => a (Fin.cast hp.symm k))
        = (0 : γ) + (∑ l, monomial (bilinE pZ₁ pZ₂ hp) a l • bilinG f pZ₁ pZ₂ l)
          + ∑ j : Fin 0, b j • (Fin.elim0 j : γ) := by
    intro a b
    rw [← PolyZonotope.bilin_point f pZ₁ pZ₂ hp a]
    show (pZ₁.bilin f pZ₂ hp).point a = (pZ₁.bilin f pZ₂ hp).point a
        + ∑ j : Fin 0, b j • (Fin.elim0 j : γ)
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨a, ha, rfl⟩
    exact ⟨a, fun _ => 0, ha, fun j => j.elim0, hpt a fun _ => 0⟩
  -- back, the same factor vector reused and the empty block read as it is
  · rintro x ⟨a, b, ha, _, hx⟩
    exact ⟨a, ha, by rw [hx]; exact hpt a b⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
