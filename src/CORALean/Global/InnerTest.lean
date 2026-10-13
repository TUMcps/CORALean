import Mathlib.Order.Interval.Set.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

/-!
# The inclusion test (5), read over real matrices

[1, Cor. 3.1]'s test `H(J, ũ, u, y₁) ⊆ int(u₁)`,
`H = ũ₁ + Diag⁻¹(J₁)(y₁ - f₁:ᵣ(ũ) - OffDiag(J₁)(u₁ - ũ₁) - J₂(u₂ - ũ₂))`, as a statement about
every real `J₁, J₂` in the interval matrices and every point of `y₁` and `u = (u₁, u₂)`: each
value of the expression lies in the open box. An interval evaluation of `H` encloses all of
them, so the paper's test implies this one. The domain is `ℝʳ × ℝᵐ⁻ʳ`, the split (3) assumes.

## References

* [1] O. Mullier, É. Goubault, M. Kieffer and S. Putot. "General Inner Approximation of
      Vector-valued Functions". Reliable Computing, 18:117-143, 2013.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Set

variable {r s : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- (5), read over real matrices: every value of `H` lies in `int(u₁)`. -/
def innerTest (g : (Fin r → ℝ) × (Fin s → ℝ) → (Fin r → ℝ)) (ũ : (Fin r → ℝ) × (Fin s → ℝ))
    (lo₁ hi₁ : Fin r → ℝ) (lo₂ hi₂ : Fin s → ℝ) (J₁lo J₁hi : Matrix (Fin r) (Fin r) ℝ)
    (J₂lo J₂hi : Matrix (Fin r) (Fin s) ℝ) (ylo yhi : Fin r → ℝ) : Prop :=
  ∀ y ∈ Icc ylo yhi, ∀ J₁ : Matrix (Fin r) (Fin r) ℝ, (∀ i j, J₁ i j ∈ Icc (J₁lo i j) (J₁hi i j)) →
    ∀ J₂ : Matrix (Fin r) (Fin s) ℝ, (∀ i l, J₂ i l ∈ Icc (J₂lo i l) (J₂hi i l)) →
    ∀ v ∈ Icc lo₁ hi₁, ∀ w ∈ Icc lo₂ hi₂, ∀ i,
      ũ.1 i + (y i - g ũ i - ∑ j ∈ Finset.univ.erase i, J₁ i j * (v j - ũ.1 j)
        - ∑ l, J₂ i l * (w l - ũ.2 l)) / J₁ i i ∈ Ioo (lo₁ i) (hi₁ i)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
