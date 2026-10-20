module

public import CORALean.ContDynamics.LinearARX.Theorems.BtildeSucc

@[expose] public section

/-!
# The next parameter from the last

[1, Lemma 3]: `B̃ᵢ₊₁(k) = Ā_ext B̃ᵢ(k) + B̄_ext,i+1 - Ā_ext^k B̄_ext,i+1-k` (16), the recursion
Alg. 1 and Alg. 2 compute their parameters with. `Btilde_succ` gives `B̃ᵢ₊₁(k+1)` both
ways — as `B̄_ext,i+1 + Ā_ext B̃ᵢ(k)`, and as `B̃ᵢ₊₁(k)` plus its last term.

## Inputs
* `sys` – ARX system
* `k` – step
* `i` – lag index

## Hypotheses
* none

## Conclusion
* the parameter at the next lag follows from the one at lag `i`

## References

* [1] L. Lützow and M. Althoff. "Reachability Analysis of ARMAX Models". In Proc. of the
  62nd IEEE Conference on Decision and Control (CDC), 2023, pp. 7027-7034.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {dy du p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearARX.Btilde_succ_index (sys : LinearARX 𝕋 dy du p) (k : ℕ) (i : ℤ) :
    sys.Btilde k (i + 1)
      = sys.Aext * sys.Btilde k i + sys.Bext (i + 1)
        - sys.Aext ^ k * sys.Bext (i + 1 - k) := by -- --- PROOF ---
  have h₁ := sys.Btilde_succ k (i + 1)
  have h₂ : sys.Btilde (k + 1) (i + 1)
      = sys.Btilde k (i + 1) + sys.Aext ^ k * sys.Bext (i + 1 - k) := by
    unfold LinearARX.Btilde
    rw [Finset.sum_range_succ]
  rw [add_sub_cancel_right] at h₁
  rw [eq_sub_iff_add_eq, ← h₂, h₁, add_comm]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
