import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Real.Basic

/-!
# A polynomial in the monomial basis, and what moves its coefficients

What a polynomial relaxation's coefficients mean, over ℝ: `evalPoly c t = ∑ c i tⁱ`, its
derivative written out so that a caller bounds it without unfolding anything, and the three
exact reshapings the pipeline performs on coefficients — the constant moved by `s` (the
recentring `computeApproxError` does), `t ↦ a · p (b · t)` (an affine conjugation, `b` folding
into the monomials one power at a time and `a` multiplying every coefficient once), and
padding to a higher degree with zeros (how the neurons of one layer meet at a common degree).
A machine scalar stores coefficients and performs the same reshapings rounded; these are what
it is proved against.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A polynomial in the monomial basis, `c i` the coefficient of `t ^ i`. -/
noncomputable def evalPoly {n : ℕ} (c : Fin (n + 1) → ℝ) (t : ℝ) : ℝ := ∑ i, c i * t ^ (i : ℕ)

/-- The derivative of `evalPoly c`, written out rather than differentiated. -/
noncomputable def evalPolyDeriv {n : ℕ} (c : Fin (n + 1) → ℝ) (t : ℝ) : ℝ :=
  ∑ i, c i * ((i : ℕ) * t ^ ((i : ℕ) - 1))

/-- The constant coefficient moved by `s`, so that what is left of an error is a radius. -/
noncomputable def shiftConst {n : ℕ} (c : Fin (n + 1) → ℝ) (s : ℝ) : Fin (n + 1) → ℝ :=
  fun i => c i + (if i = 0 then s else 0)

/-- The coefficients of `t ↦ a · p (b · t)`, where `p` has coefficients `c`. -/
noncomputable def scaleCoeffs {n : ℕ} (c : Fin (n + 1) → ℝ) (a b : ℝ) : Fin (n + 1) → ℝ :=
  fun i => a * c i * b ^ (i : ℕ)

/-- Coefficients read at degree `M`, the ones the original does not have zero. -/
noncomputable def padCoeffs {k : ℕ} (c : Fin (k + 1) → ℝ) (M : ℕ) : Fin (M + 1) → ℝ :=
  fun j => if h : (j : ℕ) < k + 1 then c ⟨(j : ℕ), h⟩ else 0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
