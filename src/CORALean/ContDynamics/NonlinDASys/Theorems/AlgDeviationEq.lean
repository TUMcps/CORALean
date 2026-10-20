module

public import CORALean.ContDynamics.NonlinDASys.NonlinDASys
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# The algebraic deviation, solved for

[1, Eq. 12]: the linearized constraint `0 = g(z*) + D Δx + E Δu + F Δy + ℓᵃ` ([1, Eq. 11]),
`F` invertible by the index-1 property, gives `Δy = -F⁻¹(g(z*) + D Δx + E Δu) - F⁻¹ ℓᵃ`.

Stated with `ℓᵃ` the one linearization error of the constraint at the point at hand, so
nothing about which set holds it: [1, Eq. 12] prints the set `{-½ F⁻¹ φ | φⱼ = νᵀH^{a,(j)}(ξ)ν,
ξ ∈ R^z, ν ∈ R^z_Δ}`, one `ξ` for all `j`, which need not hold `ℓᵃ`
(`SharedLagrangePoint`); with one `ξ⁽ʲ⁾` per row it does
(`NonlinDASys.exists_lagrange_remainder`). Only `F⁻¹ F = I` is used.

## Inputs
* `g₀` – constraint at the linearization point
* `D` – constraint Jacobian in the state
* `E` – constraint Jacobian in the input
* `F` – constraint Jacobian in the algebraic variable
* `F_inv` – inverse of `F`
* `Δx` – state deviation
* `Δu` – input deviation
* `Δy` – algebraic deviation
* `ℓa` – algebraic linearization error

## Hypotheses
* `hF` – `F_inv` is a left inverse of `F`
* `hg` – the linearized constraint holds

## Conclusion
* the algebraic deviation is determined by the other deviations

## References

* [1] M. Althoff and B. H. Krogh. "Reachability Analysis of Nonlinear Differential-Algebraic
      Systems". IEEE Transactions on Automatic Control, 59(2):371-383, 2014.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n p m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 12]: `0 = g(z*) + D Δx + E Δu + F Δy + ℓᵃ` and `F⁻¹ F = I` give
`Δy = -F⁻¹(g(z*) + D Δx + E Δu) - F⁻¹ ℓᵃ`. -/
theorem NonlinDASys.alg_deviation_eq {g₀ : Vec ℝ p} {D : Mat ℝ p n} {E : Mat ℝ p m}
    {F F_inv : Mat ℝ p p} (hF : F_inv * F = 1) {Δx : Vec ℝ n} {Δu : Vec ℝ m} {Δy ℓa : Vec ℝ p}
    (hg : g₀ + D *ᵥ Δx + E *ᵥ Δu + F *ᵥ Δy + ℓa = 0) :
    Δy = -(F_inv *ᵥ (g₀ + D *ᵥ Δx + E *ᵥ Δu)) - F_inv *ᵥ ℓa := by -- --- PROOF ---
  -- `F Δy` is the rest of the constraint, negated, and `F⁻¹` undoes `F`
  have hFy : F *ᵥ Δy = -(g₀ + D *ᵥ Δx + E *ᵥ Δu) - ℓa := by
    rw [← sub_eq_zero, ← hg]; abel
  calc Δy = F_inv *ᵥ (F *ᵥ Δy) := by rw [Matrix.mulVec_mulVec, hF, Matrix.one_mulVec]
    _ = -(F_inv *ᵥ (g₀ + D *ᵥ Δx + E *ᵥ Δu)) - F_inv *ᵥ ℓa := by
        rw [hFy, Matrix.mulVec_sub, Matrix.mulVec_neg]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
