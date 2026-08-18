import CORALean.Arithmetic.Real.ContSet.Zonotope.Operations.API

/-!
# `Zonotope.mtimes` is exactly the image under a linear map

The same coefficients work in both directions — a linear map introduces no new
freedom and removes none — so what is left is `aux_mulVec_apply`, which
distributes the sum and swaps the two summations. A linear image of a zonotope
is a zonotope, which is what the propagation loop rests on.

No `mtimes_outer` here: the float `mtimes` pays its rounding into the error box,
so it reproves this alongside the spill rather than composing with it.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   17-August-2026 (exactness)
-- Last revision: ---

namespace CORALean.Arithmetic.Real

open Matrix

variable {n m : ℕ}

/-- Mapping a point of `Z` reads the same coefficients against `mtimes M Z`. -/
theorem Zonotope.aux_mulVec_apply (M : Mat ℝ m n) (Z : Zonotope n) {x : Vec ℝ n} {β : Vec ℝ Z.h}
    (hx : ∀ l, x l = Z.c l + ∑ j, Z.G l j * β j) (i : Fin m) :
    (M *ᵥ x) i = (Zonotope.mtimes M Z).c i + ∑ j, (Zonotope.mtimes M Z).G i j * β j := by
  have expand : ∀ l, M i l * x l = M i l * Z.c l + ∑ j, M i l * Z.G l j * β j := by
    intro l
    rw [hx l, mul_add, Finset.mul_sum]
    simp_rw [mul_assoc]
  simp only [Zonotope.mtimes, Matrix.mulVec, dotProduct, Matrix.mul_apply,
    Finset.sum_mul]
  rw [Finset.sum_congr rfl fun l _ => expand l, Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_comm

theorem Zonotope.mtimes_exact (M : Mat ℝ m n) (Z : Zonotope n) :
    (M *ᵥ ·) '' Z.construct = (Zonotope.mtimes M Z).construct := by
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨x, ⟨β, hβ, hx⟩, rfl⟩
    exact ⟨β, hβ, fun i => Zonotope.aux_mulVec_apply M Z hx i⟩
  · rintro y ⟨β, hβ, hy⟩
    refine ⟨fun l => Z.c l + ∑ j, Z.G l j * β j, ⟨β, hβ, fun _ => rfl⟩, ?_⟩
    funext i
    exact (Zonotope.aux_mulVec_apply M Z (fun _ => rfl) i).trans (hy i).symm

end CORALean.Arithmetic.Real
