module

public import CORALean.ContSet.Zonotope.Real.Theorems.MemConstruct
public import CORALean.Specification.STL.Operations.DepBox
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# A real zonotope reaches the extremes of its row sums

In each coordinate `i` a real zonotope holds points at `c_i + Σ_l |G_{i,l}|` and at
`c_i - Σ_l |G_{i,l}|`: the coefficient of a generator is the sign of its entry in that coordinate.
So the interval hull of the zonotope is the box of `STL.depBox` and its reach `|c_i| + Σ_l
|G_{i,l}|` is the largest absolute value of the coordinate.

## Inputs
* `Z` – real zonotope
* `i` – coordinate

## Hypotheses
* none

## Conclusion
* points of the zonotope reach both extremes of the coordinate
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A real zonotope reaches `c_i ± Σ_l |G_{i,l}|` in coordinate `i`. -/
theorem STL.zonotope_extremes (Z : Real.Zonotope (Vec ℝ n)) (i : Fin n) : -- --- CONCL ---
    (∃ x ∈ Z.construct, x i = Z.c i + ∑ l, |Z.G l i|) ∧
      ∃ x ∈ Z.construct, x i = Z.c i - ∑ l, |Z.G l i| := by -- --- PROOF ---
  -- the signs of the generators in coordinate `i` push the coordinate to the extreme
  have key : ∀ σ : ℝ, |σ| = 1 → ∃ x ∈ Z.construct,
      x i = Z.c i + ∑ l, σ * (|Z.G l i|) := by
    intro σ hσ
    let β : Fin Z.h → ℝ := fun l => σ * (if 0 ≤ Z.G l i then 1 else -1)
    have hβ : ∀ l, |β l| ≤ 1 := fun l => by
      simp only [β, abs_mul, hσ, one_mul]
      split_ifs <;> simp
    refine ⟨fun j => Z.c j + ∑ l, Z.G l j * β l,
      Real.Zonotope.mem_construct_iff.2 ⟨β, hβ, fun _ => rfl⟩, ?_⟩
    simp only [β]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    -- each term is `σ` times the absolute value, whichever sign the entry has
    split_ifs with h
    · rw [abs_of_nonneg h]; ring
    · rw [abs_of_neg (not_le.1 h)]; ring
  -- the signs `1` and `-1` give the upper and the lower extreme
  obtain ⟨x, hx, e⟩ := key 1 (by simp)
  obtain ⟨x', hx', e'⟩ := key (-1) (by simp)
  refine ⟨⟨x, hx, ?_⟩, ⟨x', hx', ?_⟩⟩
  · rw [e]; simp
  · rw [e']; simp [Finset.sum_neg_distrib, sub_eq_add_neg]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
