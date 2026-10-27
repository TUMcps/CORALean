module

public import CORALean.ContDynamics.LinearARX.Theorems.BextEqZero
public import CORALean.ContDynamics.LinearARX.Theorems.BtildeSucc

@[expose] public section

/-!
# Later parameters from earlier ones

[1, Lemma 1]: `Ã(k+Δk) = Ā_ext^Δk Ã(k)` (14a), and for `i ≥ p + Δk`,
`B̃ᵢ(k+Δk) = Ā_ext^Δk B̃ᵢ₋Δk(k)` (14b). By induction on `Δk` through `Btilde_succ`, the
`B̄_ext,i` it adds being zero because `i > p`. What lets Alg. 1 and Alg. 2 multiply
the older sets by `Ā_ext^p` instead of recomputing them.

## Inputs
* `sys` – ARX system
* `k` – step
* `Δk` – step increment

## Hypotheses
* none

## Conclusion
* later parameters follow from earlier ones by powers of the extended matrix

## References

* [1] [L. Lützow and M. Althoff. "Reachability Analysis of ARMAX Models". 2023 62nd IEEE Conference
      on Decision and Control (CDC), 2023.](../../../../../references/2023/luetzow-cdc-armax.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {dy du p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearARX.Btilde_add_of_le (sys : LinearARX 𝕋 dy du p) (k Δk : ℕ) : -- --- CONCL ---
    sys.Aext ^ (k + Δk) = sys.Aext ^ Δk * sys.Aext ^ k ∧
    ∀ i : ℤ, (p : ℤ) + Δk ≤ i →
      sys.Btilde (k + Δk) i = sys.Aext ^ Δk * sys.Btilde k (i - Δk) := by -- --- PROOF ---
  refine ⟨by rw [add_comm, pow_add], ?_⟩
  induction Δk with
  | zero =>
    intro i _
    rw [add_zero, pow_zero, Matrix.one_mul, Nat.cast_zero, sub_zero]
  | succ n ih =>
    intro i hi
    rw [← add_assoc, LinearARX.Btilde_succ, sys.Bext_eq_zero (Or.inr (by push_cast at hi; omega)),
      zero_add, ih (i - 1) (by push_cast at hi; omega), ← Matrix.mul_assoc, ← pow_succ']
    congr 2
    push_cast
    ring

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
