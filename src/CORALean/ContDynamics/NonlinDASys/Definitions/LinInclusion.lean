module

public import CORALean.ContDynamics.NonlinDASys.NonlinDASys
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# The linear differential inclusion abstracting a DAE

[1, Eq. 14] and [1, Eq. 16]: linearized at `z* = (x*, y*, u*)` with Jacobian blocks
`∂f/∂z = [A, C, B]`, `∂g/∂z = [D, F, E]` ([1, Eq. 9]), the algebraic deviation eliminated through
`F⁻¹` (index 1), the differential variables obey `˙x̃ ∈ Ã x̃ ⊕ Ũ`, `x̃ = Δx`, with
`w = f(z*) - C F⁻¹ g(z*)`, `Ã = A - C F⁻¹ D`, `B̃ = B - C F⁻¹ E` and `Ũ = w ⊕ B̃ (U ⊕ (-u*)) ⊕ L`,
`L` the set of linearization errors. `linInclusion` is the right-hand side `Ã Δx ⊕ Ũ` at one `Δx`.
`F⁻¹` is a parameter, a left inverse of `F` wherever a theorem needs one; `f(z*)`, `g(z*)` are
passed as values. `L` is any set; which errors it must hold is the hypothesis of the theorems
that use it.

## Inputs
* `f₀` – dynamics at the linearization point
* `g₀` – constraint at the linearization point
* `A` – dynamics Jacobian in the state
* `B` – dynamics Jacobian in the input
* `C` – dynamics Jacobian in the algebraic variable
* `D` – constraint Jacobian in the state
* `E` – constraint Jacobian in the input
* `F_inv` – inverse of the constraint Jacobian in the algebraic variable
* `us` – linearization input
* `U` – input set
* `L` – linearization error set
* `Δx` – state deviation

## Output
* the right-hand side of the differential inclusion at the deviation

## References

* [1] M. Althoff and B. H. Krogh. "Reachability Analysis of Nonlinear Differential-Algebraic
      Systems". IEEE Transactions on Automatic Control, 2014.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix
open scoped Pointwise

variable {n p m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Eq. 14], [1, Eq. 16]: `Ã Δx ⊕ Ũ`, `Ũ = w ⊕ B̃ (U ⊕ (-u*)) ⊕ L`. -/
def NonlinDASys.linInclusion (f₀ : Vec ℝ n) (g₀ : Vec ℝ p) (A : Mat ℝ n n) (B : Mat ℝ n m)
    (C : Mat ℝ n p) (D : Mat ℝ p n) (E : Mat ℝ p m) (F_inv : Mat ℝ p p) (us : Vec ℝ m)
    (U : Set (Vec ℝ m)) (L : Set (Vec ℝ n)) (Δx : Vec ℝ n) : Set (Vec ℝ n) :=
  let w : Vec ℝ n := f₀ - (C * F_inv) *ᵥ g₀                       -- (14)
  let A_t : Mat ℝ n n := A - C * F_inv * D                          -- (14), Ã
  let B_t : Mat ℝ n m := B - C * F_inv * E                          -- (14), B̃
  let U_t : Set (Vec ℝ n) := {w} + (B_t *ᵥ ·) '' ((· - us) '' U) + L  -- (16), Ũ
  {A_t *ᵥ Δx} + U_t                                                 -- (16), Ã x̃ ⊕ Ũ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
