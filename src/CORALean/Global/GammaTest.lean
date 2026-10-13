module

public import Mathlib.Order.Interval.Set.Pi
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

@[expose] public section

/-!
# The inclusion `x̃ + Γ(J, x - x̃, y - f(x̃)) ⊆ int x`

[1, Cor. 3.1], (2): with `Γ(A, u, b) = Diag⁻¹(A) (b - OffDiag(A) u)` the condition that `Γ`
of the interval matrix `J = [Jlo, Jhi]`, of `x - x₀` (`x₀` is the paper's `x̃`) and of
`y - f(x₀)` lies, shifted by `x₀`, in the interior of the box `x = [xlo, xhi]`. Each
component `i` reads `x₀ᵢ + (yᵢ - f(x₀)ᵢ - Σ_{j≠i} Jᵢⱼ (vⱼ - x₀ⱼ)) / Jᵢᵢ ∈ (xloᵢ, xhiᵢ)`, for
every real matrix `J` in the bounds, `y ∈ y` and `v ∈ x`. This is the range of the interval
evaluation, which is exact here: each of `Jᵢᵢ`, `Jᵢⱼ`, `vⱼ`, `yᵢ` occurs once.

## References

* [1] A. Goldsztejn and L. Jaulin. "Inner approximation of the range of vector-valued
      functions". Reliable Computing, 14:1-23, 2010.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Set

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Cor. 3.1], (2): `x₀ + Γ(J, x - x₀, y - f(x₀)) ⊆ int x`, read over the real points. -/
def gammaTest (f : (Fin n → ℝ) → (Fin n → ℝ)) (x₀ xlo xhi : Fin n → ℝ)
    (Jlo Jhi : Matrix (Fin n) (Fin n) ℝ) (ylo yhi : Fin n → ℝ) : Prop :=
  ∀ y ∈ Icc ylo yhi, ∀ J : Matrix (Fin n) (Fin n) ℝ, (∀ i j, J i j ∈ Icc (Jlo i j) (Jhi i j)) →
    ∀ v ∈ Icc xlo xhi, ∀ i,
      x₀ i + (y i - f x₀ i - ∑ j ∈ Finset.univ.erase i, J i j * (v j - x₀ j)) / J i i
        ∈ Ioo (xlo i) (xhi i)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
