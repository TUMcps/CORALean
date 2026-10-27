module

public import CORALean.ContDynamics.LinearARX.LinearARX

@[expose] public section

/-!
# The exact reachable outputs

[1, Prop. 3]'s `Y(k)`: every output `y(k)` some ARMAX run reaches from the measured first window
`ỹ_init` under inputs `ũ(i) ∈ Ũ(i)` (Problem statement, Sec. II-E). The inputs are one
signal for all time, which is what makes `Y(k)` and `Y(k+1)` dependent.

## Inputs
* `sys` – ARX system
* `y₀` – measured first output window
* `U` – input sets per step
* `k` – step

## Output
* the outputs some run reaches at step `k`

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

def LinearARX.reachOutExact (sys : LinearARX 𝕋 dy du p) (y₀ : Vec ℝ (p * dy))
    (U : ℕ → Set (Vec ℝ du)) (k : ℕ) : Set (Vec ℝ dy) :=
  {x | ∃ (y : ℕ → Vec ℝ dy) (u : ℕ → Vec ℝ du), LinearARX.stack p y 0 = y₀ ∧ (∀ i, u i ∈ U i) ∧
    (∀ k, p ≤ k → y k = ∑ i : Fin p, toRealMat (sys.Abar i) *ᵥ y (k - (i + 1))
      + ∑ j : Fin (p + 1), toRealMat (sys.Bbar j) *ᵥ u (k - j)) ∧
    x = y k}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
