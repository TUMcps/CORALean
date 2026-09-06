import CORALean.ContSet.ConZonotope.Real.ConZonotope

/-!
# A constrained zonotope is convex

The affine image of a polytope. Read off the coefficients: a weighted average of
two admissible ones stays in the unit box, and stays in `P` because a polytope is
convex — that second half is all the constraints add over a zonotope, and it is
`HPolytope.convex_construct` rather than an argument of its own.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.convex_construct (C : ConZonotope α) :
    Convex ℝ C.construct := by -- --- PROOF ---
  rintro x ⟨β₁, hβ₁, hP₁, rfl⟩ y ⟨β₂, hβ₂, hP₂, rfl⟩ s t hs ht hst
  have hbox : ∀ j, |s * β₁ j + t * β₂ j| ≤ 1 := by
    intro j
    have h1 : |s * β₁ j| ≤ s := by
      rw [abs_mul, abs_of_nonneg hs]
      calc s * |β₁ j| ≤ s * 1 := mul_le_mul_of_nonneg_left (hβ₁ j) hs
        _ = s := mul_one s
    have h2 : |t * β₂ j| ≤ t := by
      rw [abs_mul, abs_of_nonneg ht]
      calc t * |β₂ j| ≤ t * 1 := mul_le_mul_of_nonneg_left (hβ₂ j) ht
        _ = t := mul_one t
    calc |s * β₁ j + t * β₂ j| ≤ |s * β₁ j| + |t * β₂ j| := abs_add_le _ _
      _ ≤ s + t := add_le_add h1 h2
      _ = 1 := hst
  -- the constraints are a polytope, and a polytope is convex
  have hP : s • β₁ + t • β₂ ∈ C.P.construct :=
    HPolytope.convex_construct C.P hP₁ hP₂ hs ht hst
  have hval : ∑ j, (s * β₁ j + t * β₂ j) • C.G j
      = s • (∑ j, β₁ j • C.G j) + t • ∑ j, β₂ j • C.G j := by
    rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [add_smul, smul_smul, smul_smul]
  refine ⟨fun j => s * β₁ j + t * β₂ j, hbox, hP, ?_⟩
  calc s • (C.c + ∑ j, β₁ j • C.G j) + t • (C.c + ∑ j, β₂ j • C.G j)
      = (s + t) • C.c + (s • (∑ j, β₁ j • C.G j) + t • ∑ j, β₂ j • C.G j) := by
        rw [smul_add, smul_add, add_smul]; abel
    _ = C.c + ∑ j, (s * β₁ j + t * β₂ j) • C.G j := by rw [hst, one_smul, hval]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
