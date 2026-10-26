module

public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.ArnoldiBasisMulVecPow
public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.AugmentPowMulVec

@[expose] public section

/-!
# The Krylov Taylor terms of an input are its exact Taylor terms

The terms of [1, Thm. IV.2] and [1, Cor. IV.2], `P Ṽ(u) H̃ʲ(u) e₁`, with `Ṽ(u), H̃(u)` from
Alg. 1 after `ξ = m + 1` passes at `C̃ = [A u; 0 0]`, `ṽ = [0ₙ; 1]` (`Lemma IV.1`), are
`A^{j-1} u` for `1 ≤ j ≤ m`: `Ṽ H̃ʲ e₁ = C̃ʲ ṽ` below the Krylov order
(`arnoldiBasis_mulVec_pow`, `‖ṽ‖ = 1`), and `C̃ʲ ṽ = [A^{j-1} u; 0]`. So below the Krylov
order the set `P D⁽ʲ⁾ e₁` of [1]'s Appendix A is the linear image `A^{j-1} U / j!`.

## Inputs
* `A` – system matrix
* `u` – constant input
* `m` – Krylov order
* `j` – power

## Hypotheses
* `hj1` – power at least one
* `hj` – power at most the Krylov order

## Conclusion
* the Krylov Taylor term equals the exact Taylor term

## References

* [1] M. Althoff. "Reachability Analysis of Large Linear Systems with Uncertain Inputs in the Krylov
      Subspace". IEEE Transactions on Automatic Control, 2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `‖[0ₙ; 1]‖ = 1`. -/
private theorem Krylov.aux_norm₂_single_last : -- --- CONCL ---
    ‖(Pi.single (Fin.last n) 1 : Fin (n + 1) → ℝ)‖₂ = 1 := by -- --- PROOF ---
  set e : Fin (n + 1) → ℝ := Pi.single (Fin.last n) 1 with he
  have h : ∀ i, e i ^ 2 = e i := by
    intro i
    by_cases hi : i = Fin.last n
    · rw [hi, he, Pi.single_eq_same, one_pow]
    · rw [he, Pi.single_eq_of_ne hi, zero_pow two_ne_zero]
  rw [norm₂, Finset.sum_congr rfl fun i _ => h i, he, Finset.sum_pi_single',
    if_pos (Finset.mem_univ _), Real.sqrt_one]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `P Ṽ(u) H̃ʲ(u) e₁ = A^{j-1} u` for `1 ≤ j ≤ m`, Alg. 1 run `m + 1` passes. -/
theorem Krylov.augment_arnoldi_pow (A : Mat ℝ n n) (u : Vec ℝ n) (m : ℕ) {j : ℕ} (hj1 : 1 ≤ j)
    (hj : j ≤ m) : -- --- CONCL ---
    (fun i => (Krylov.arnoldiBasis (Krylov.augment A u) (Pi.single (Fin.last n) 1) (m + 1) *ᵥ
        (Krylov.arnoldiHessenberg (Krylov.augment A u) (Pi.single (Fin.last n) 1) (m + 1) ^ j *ᵥ
          Pi.single 0 1)) (Fin.castSucc i))
      = A ^ (j - 1) *ᵥ u := by -- --- PROOF ---
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  rw [Krylov.arnoldiBasis_mulVec_pow _ _ m hj, Krylov.aux_norm₂_single_last, inv_one, one_smul,
    Nat.add_sub_cancel]
  exact (Krylov.augment_pow_mulVec A u k).1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
