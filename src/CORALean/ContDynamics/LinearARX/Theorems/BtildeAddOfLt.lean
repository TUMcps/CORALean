module

public import CORALean.ContDynamics.LinearARX.Theorems.BextEqZero
public import CORALean.ContDynamics.LinearARX.Operations.Btilde

@[expose] public section

/-!
# Settled parameters

[1, Lemma 2]: for `i < k`, `B̃ᵢ(k+Δk) = B̃ᵢ(k)`. The terms `j ≥ k` that `k + Δk` adds
to (9b) of [1, Thm. 1] carry `B̄_ext,i-j` with `i - j < 0`, which is zero.

## Inputs
* `sys` – ARX system
* `k` – step
* `Δk` – step increment
* `i` – lag index

## Hypotheses
* `hi` – lag below the step

## Conclusion
* the parameter at lag `i` is unchanged by later steps

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

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {dy du p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearARX.Btilde_add_of_lt (sys : LinearARX 𝕋 dy du p) (k Δk : ℕ) {i : ℤ}
    (hi : i < k) : sys.Btilde (k + Δk) i = sys.Btilde k i := by
  unfold LinearARX.Btilde
  rw [Finset.sum_range_add, add_eq_left]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [sys.Bext_eq_zero (Or.inl (by push_cast; omega)), Matrix.mul_zero]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
