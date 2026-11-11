module

public import CORALean.ContDynamics.LinearSys.Krylov.Operations.ArnoldiFloat
public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# The float Arnoldi iteration stores an upper Hessenberg matrix

Pass `k` of [1, Alg. 1] writes column `k` of `H` from the rows `0, …, k + 1` only, and the start has
none, so every entry below the subdiagonal stays zero: the shape the error bound reads from the
stored matrix, however the vectors came out.

## Inputs
* `p` – Newton steps per norm
* `ε` – breakdown threshold
* `A` – matrix
* `c` – start vector
* `ν` – scale
* `k` – number of passes

## Hypotheses
* none

## Conclusion
* the stored entries below the subdiagonal read as zero

## References

* [1] [M. Althoff. "Reachability Analysis of Large Linear Systems with Uncertain Inputs in the
      Krylov Subspace". IEEE Transactions on Automatic Control,
      2020.](../../../../../../references/2020/althoff-tac-krylov.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- One pass keeps the zeros and writes none below the subdiagonal. -/
private theorem aux_pass (p : ℕ) (ε : 𝕋) (A : Mat 𝕋 n n) (k : ℕ)
    (st : (ℕ → Vector 𝕋 n) × (ℕ → ℕ → 𝕋))
    (h : ∀ i j, j + 1 < i → toReal (st.2 i j) = 0) : -- --- CONCL ---
    ∀ i j, j + 1 < i →
      toReal ((Krylov.step_arnoldiPass p ε A k st).2 i j) = 0 := by -- --- PROOF ---
  intro i j hij
  simp only [Krylov.step_arnoldiPass]
  by_cases hjk : j = k
  · subst hjk
    have h1 : ¬ i ≤ j := by omega
    have h2 : ¬ i = j + 1 := by omega
    simp [h1, h2, toReal_zero]
  · simp [hjk, h i j hij]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Entries of the stored Hessenberg matrix below the subdiagonal read as zero. -/
theorem Krylov.arnoldiFloat_hessenberg (p : ℕ) (ε : 𝕋) (A : Mat 𝕋 n n) (c : Vec 𝕋 n) (ν : 𝕋)
    (k : ℕ) : -- --- CONCL ---
    ∀ i j, j + 1 < i → toReal ((Krylov.arnoldiFloat p ε A c ν k).2 i j) = 0 := by -- --- PROOF ---
  induction k with
  | zero =>
    intro i j _
    simp [Krylov.arnoldiFloat, Krylov.step_arnoldiStart, toReal_zero]
  | succ k ih => exact aux_pass p ε A k _ ih

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
