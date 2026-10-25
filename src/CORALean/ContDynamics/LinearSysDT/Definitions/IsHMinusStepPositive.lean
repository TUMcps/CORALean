module

public import CORALean.ContDynamics.LinearSysDT.LinearSysDT
public import Mathlib.LinearAlgebra.Matrix.PosDef

@[expose] public section

/-!
# The `H₋` step condition of the fault-detection observer

[1, Eq. 24]: with the fault-only error `e` following `e⁺ = (A - LC) e - LE f` [1, Eq. 19], the
residual center `p = MCe + MEf` [1, Eq. 20] and the Lyapunov function `V = eᵀQe` [1, Eq. 22], the
quantity `pᵀp - β²fᵀf - (V⁺ - V)` is positive for every `(e, f) ≠ 0`. It is the form
`≻ 0` of [1, Eq. 24] read at the pair `(e, f)` it is a function of.

## Inputs
* `A` – state matrix
* `C` – output matrix
* `E` – fault matrix
* `L` – observer gain
* `Q` – Lyapunov matrix
* `M` – residual weight
* `β` – sensitivity level

## Output
* the step quantity is positive at every nonzero error and fault

## References

* [1] Y. Wang, M. Zhou, V. Puig, G. Cembrano and Z. Wang. "Zonotopic Fault Detection Observer with
      H₋ Performance". 2017 36th Chinese Control Conference (CCC), 2017.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n ny nf : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Eq. 24]: `p^{rf}ᵀp^{rf} - β²fᵀf - ΔV` is positive at every `(e, f) ≠ 0`. -/
def LinearSysDT.IsHMinusStepPositive (A : Mat ℝ n n) (C : Mat ℝ ny n) (E : Mat ℝ ny nf)
    (L : Mat ℝ n ny) (Q : Mat ℝ n n) (M : Mat ℝ ny ny) (β : ℝ) : Prop :=
  ∀ (e : Vec ℝ n) (f : Vec ℝ nf), (Sum.elim e f : Fin n ⊕ Fin nf → ℝ) ≠ 0 →
    let w := (A - L * C) *ᵥ e - (L * E) *ᵥ f                                  -- Eq. 19, `e⁺`
    let p := (M * C) *ᵥ e + (M * E) *ᵥ f                                      -- Eq. 20
    0 < p ⬝ᵥ p - β ^ 2 * (f ⬝ᵥ f) - (w ⬝ᵥ (Q *ᵥ w) - e ⬝ᵥ (Q *ᵥ e))         -- Eq. 24, Eq. 22

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
