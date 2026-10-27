module

public import CORALean.ContDynamics.LinearARX.LinearARX

@[expose] public section

/-!
# The exact reachable windows

Every window `ỹ(k:k₊) = (y(k), …, y(k+p-1))` some ARMAX run reaches from the measured first
window `ỹ_init` under inputs `ũ(i) ∈ Ũ(i)`: the set [1, Eq. 12] computes, taken jointly.
Its (13) writes it as the Cartesian product `Y(k) × ⋯ × Y(k₊)`, which it is not;
`reachWindowExact_ne_prod` is the counterexample.

## Inputs
* `sys` – ARX system
* `y₀` – measured first output window
* `U` – input sets per step
* `k` – step

## Output
* the output windows some run reaches at step `k`

## References

* [1] [L. Lützow and M. Althoff. "Reachability Analysis of ARMAX Models". 2023 62nd IEEE Conference
      on Decision and Control (CDC), 2023.](../../../../../references/2023/luetzow-cdc-armax.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar

variable {𝕋 : Type} [Scalar 𝕋] {dy du p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def LinearARX.reachWindowExact (sys : LinearARX 𝕋 dy du p) (y₀ : Vec ℝ (p * dy))
    (U : ℕ → Set (Vec ℝ du)) (k : ℕ) : Set (Vec ℝ (p * dy)) :=
  {w | ∃ (y : ℕ → Vec ℝ dy) (u : ℕ → Vec ℝ du), LinearARX.stack p y 0 = y₀ ∧ (∀ i, u i ∈ U i) ∧
    (∀ k, p ≤ k → y k = ∑ i : Fin p, toRealMat (sys.Abar i) *ᵥ y (k - (i + 1))
      + ∑ j : Fin (p + 1), toRealMat (sys.Bbar j) *ᵥ u (k - j)) ∧
    w = LinearARX.stack p y k}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
