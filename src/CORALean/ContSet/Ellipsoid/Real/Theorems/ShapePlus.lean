import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
import CORALean.ContSet.Ellipsoid.Real.Operations.Plus
import CORALean.ContSet.Ellipsoid.Real.Operations.Shape

/-!
# The shape of the enclosing ellipsoid of a Minkowski sum

The generators of `Ellipsoid.plus s₁ s₂ E₁ E₂` are the two generator matrices scaled and
side by side, `[s₁ G₁ | s₂ G₂]`, so its shape matrix is `[s₁ G₁ | s₂ G₂]` times its transpose,
`s₁² Q₁ + s₂² Q₂`. At `s₁ = √(1 + 1/β)`, `s₂ = √(1 + β)` that is [1, Eq. 11],
`Q(β) = (1 + 1/β) Q₁ + (1 + β) Q₂`.

## References

* [1] A. Halder. "On the parameterized computation of minimum volume outer ellipsoid of
      Minkowski sum of ellipsoids". In Proc. of the 57th IEEE Conference on Decision and
      Control (CDC), pp. 4040-4045, 2018. arXiv:1803.08157.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The shape of `plus` is `s₁² Q₁ + s₂² Q₂`, which is [1, Eq. 11] at the Kurzhanski scalings. -/
theorem Ellipsoid.shape_plus (s₁ s₂ : ℝ) (E₁ E₂ : Ellipsoid n) :
    (Ellipsoid.plus s₁ s₂ E₁ E₂).shape
      = (s₁ ^ 2) • E₁.shape + (s₂ ^ 2) • E₂.shape := by -- --- PROOF ---
  ext i j
  have key : ∀ f : Fin (E₁.k + E₂.k) → ℝ, ∑ k, f k
      = ∑ k, f (Fin.castAdd E₂.k k) + ∑ k, f (Fin.natAdd E₁.k k) := fun f => Fin.sum_univ_add f
  show ∑ k : Fin (E₁.k + E₂.k), (Ellipsoid.plus s₁ s₂ E₁ E₂).G i k
      * (Ellipsoid.plus s₁ s₂ E₁ E₂).G j k = _
  rw [key]
  -- each block of generators contributes its own scaled shape
  simp only [Ellipsoid.plus, Matrix.of_apply, Fin.append_left, Fin.append_right,
    Ellipsoid.shape, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.transpose_apply,
    smul_eq_mul, Finset.mul_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun k _ => by ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
