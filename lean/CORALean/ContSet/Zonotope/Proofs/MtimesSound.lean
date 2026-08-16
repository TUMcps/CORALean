import CORALean.ContSet.Zonotope.API

/-!
# `Zonotope.mtimes` over-approximates the image under a linear map

The same coefficients work -- a linear map introduces no new freedom -- so what
is left is distributing the sum and swapping the two summations. The inclusion
is an equality: a linear image of a zonotope is a zonotope, which is what the
propagation loop rests on.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Zonotope.Proofs

open Matrix

variable {n m h : ℕ}

theorem mtimes_sound (M : Mat m n) (Z : Zonotope n h) :
    (M *ᵥ ·) '' Z.construct ⊆ (Zonotope.mtimes M Z).construct := by
  rintro _ ⟨x, ⟨β, hβ, hx⟩, rfl⟩
  refine ⟨β, hβ, fun i => ?_⟩
  have expand : ∀ k, M i k * x k = M i k * Z.c k + ∑ j, M i k * Z.G k j * β j := by
    intro k
    rw [hx k, mul_add, Finset.mul_sum]
    simp_rw [mul_assoc]
  simp only [Zonotope.mtimes, Matrix.mulVec, dotProduct, Matrix.mul_apply,
    Finset.sum_mul]
  rw [Finset.sum_congr rfl fun k _ => expand k, Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_comm

end CORALean.Zonotope.Proofs
