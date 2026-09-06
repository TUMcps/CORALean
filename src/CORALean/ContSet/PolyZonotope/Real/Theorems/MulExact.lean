import CORALean.ContSet.PolyZonotope.Real.Theorems.MulPoint

/-!
# `PolyZonotope.mul` is exactly the product over shared factors

What exactness can mean here, and what it cannot: `construct (mul S₁ S₂)` is not
`construct S₁ * construct S₂`. Both sets are functions of one shared factor
vector, so their pointwise product ranges over far fewer points than the product
of the two sets. The claim is about the evaluation map — the result is exactly
the image of the admissible factors under `a ↦ point S₁ a ⊙ point S₂ a`, with
`S₂` read at the same factors through `Fin.cast`.

`mul_point` gives that fact directly, `mul`'s own point unfolding to the sum
this file reads it back through.

The independent blocks are not hypothesised away: `point` ignores them, so they
take no part on either side.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   06-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open PolyZonotope

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.mul_exact (S₁ S₂ : PolyZonotope (Vec ℝ n)) (hp : S₁.p = S₂.p) :
    (fun a : Fin S₁.p → ℝ => S₁.point a * S₂.point (fun k => a (Fin.cast hp.symm k)))
        '' {a | ∀ k, |a k| ≤ 1}
      = (S₁.mul S₂ hp).construct := by
  -- the result has an empty independent block, so a point of it is the sum alone
  have hpt : ∀ (a : Fin S₁.p → ℝ) (b : Fin 0 → ℝ),
      S₁.point a * S₂.point (fun k => a (Fin.cast hp.symm k))
        = (0 : Vec ℝ n) + (∑ l, monomial (mulE S₁ S₂ hp) a l • mulG S₁ S₂ l)
          + ∑ j : Fin 0, b j • (Fin.elim0 j : Vec ℝ n) := by
    intro a b
    rw [← PolyZonotope.mul_point S₁ S₂ hp a]
    show (S₁.mul S₂ hp).point a = (S₁.mul S₂ hp).point a
        + ∑ j : Fin 0, b j • (Fin.elim0 j : Vec ℝ n)
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨a, ha, rfl⟩
    exact ⟨a, fun _ => 0, ha, fun j => j.elim0, hpt a fun _ => 0⟩
  -- back, the same factor vector reused and the empty block read as it is
  · rintro x ⟨a, b, ha, _, hx⟩
    exact ⟨a, ha, by rw [hx]; exact hpt a b⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
