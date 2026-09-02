import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
import CORALean.Global.LinProg.API

/-!
# An ellipsoid answers any direction in closed form

`sup {⟨d, x⟩ | x ∈ E}` is `⟨d, q⟩ + ‖Gᵀ d‖₂`. Unlike a halfspace description
there is no linear program to solve and no dual solution to check: Cauchy–Schwarz
is the whole of the `≤` direction, and the bound holds for *every* direction at
once rather than for the ones a caller enumerated. That is what makes the
conversions out of an ellipsoid tight rather than merely sound.

A functional on `Vec ℝ n` is a dot product, and `dualVec` is the vector it is
one with. The support value is stated against `Gᵀ` applied to that vector, which
lives in the generator space `Vec ℝ E.k` — the reason it is a norm on `k`
coordinates and not on `n`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {n : ℕ}

/-- The direction a functional is: `c` acts as the dot product with this vector,
which is what lets the support value be written with `Gᵀ`. -/
noncomputable def dualVec (c : Vec ℝ n →ₗ[ℝ] ℝ) : Vec ℝ n :=
  fun i => c fun j => if i = j then 1 else 0

theorem apply_eq_dotProduct (c : Vec ℝ n →ₗ[ℝ] ℝ) (x : Vec ℝ n) : c x = dualVec c ⬝ᵥ x := by
  rw [LinearMap.pi_apply_eq_sum_univ c x, dotProduct]
  exact Finset.sum_congr rfl fun i _ => by rw [smul_eq_mul]; exact mul_comm _ _

/-- The direction pulled back into generator space, which is what the support
value is the length of. -/
noncomputable def Ellipsoid.pullback (E : Ellipsoid n) (c : Vec ℝ n →ₗ[ℝ] ℝ) : Vec ℝ E.k :=
  E.Gᵀ *ᵥ dualVec c

theorem Ellipsoid.apply_mulVec (E : Ellipsoid n) (c : Vec ℝ n →ₗ[ℝ] ℝ) (u : Vec ℝ E.k) :
    c (E.G *ᵥ u) = E.pullback c ⬝ᵥ u := by
  rw [apply_eq_dotProduct, dotProduct_mulVec, Ellipsoid.pullback, mulVec_transpose]

/-- No linear program and no dual solution: the value is closed form and the
maximum is attained, which `Theorems.SupportBoundAttained` states. -/
noncomputable def Ellipsoid.supportBound (E : Ellipsoid n) (c : Vec ℝ n →ₗ[ℝ] ℝ) :
    SupportBound E.construct c where
  val := c E.q + ‖E.pullback c‖₂
  le := by
    rintro _ ⟨u, hu, rfl⟩
    rw [map_add]
    refine add_le_add le_rfl ?_
    calc c (E.G *ᵥ u) = E.pullback c ⬝ᵥ u := E.apply_mulVec c u
      _ ≤ ‖E.pullback c‖₂ * ‖u‖₂ := dotProduct_le_norm₂_mul_norm₂ _ _
      _ ≤ ‖E.pullback c‖₂ * 1 := mul_le_mul_of_nonneg_left hu (norm₂_nonneg _)
      _ = ‖E.pullback c‖₂ := mul_one _

end CORALean.Real
