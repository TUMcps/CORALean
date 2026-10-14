module

public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.HessenbergPowApplyEqZero
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# The first nonzero entry of a Hessenberg power in the first column

[1, Eq. 2.5]: `γ_m = e_mᵀ T_m^{m-1} e₁ = ∏_{j=1}^{m-1} (T_m)_{j+1,j}`, from the upper Hessenberg
structure of `T_m`. By induction on the power `k`: of `(T^{k+1})_{k+1,1} = Σ_l T_{k+1,l}(T^k)_{l,1}`
only `l = k` survives, `T_{k+1,l}` vanishing for `l < k` and `(T^k)_{l,1}` for `l > k`
(`hessenberg_pow_apply_eq_zero`). Over any commutative semiring, so for the complex `T_m`
of [1]. `γ_m` is the factor of the bound Err_a in [1, Thm. 1].

## References

* [1] T. Jawecki, W. Auzinger, O. Koch. "Computable upper error bounds for Krylov approximations
  to matrix exponentials and associated φ-functions". BIT Numerical Mathematics, 60(1):157-197,
  2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {R : Type*} [CommSemiring R] {m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `(Tᵏ)_{k,0} = ∏_{j<k} T_{j+1,j}` for every `k ≤ m` (rows and columns from `0`). -/
theorem Krylov.aux_hessenberg_pow_apply_eq_prod (T : Mat R (m + 1) (m + 1))
    (hT : ∀ i k : Fin (m + 1), (k : ℕ) + 1 < i → T i k = 0) :
    ∀ (k : ℕ) (hk : k ≤ m),
      (T ^ k) ⟨k, by omega⟩ 0
        = ∏ j : Fin k, T ⟨j + 1, by omega⟩ ⟨j, by omega⟩ := by -- --- PROOF ---
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    -- of `Σ_l T_{k+1,l}(Tᵏ)_{l,0}` only `l = k` survives
    rw [pow_succ', Matrix.mul_apply, Finset.sum_eq_single ⟨k, by omega⟩, ih (by omega),
      Fin.prod_univ_castSucc, mul_comm]
    · rfl
    · intro l _ hl
      by_cases hlk : (l : ℕ) < k
      · rw [hT _ _ (by simp; omega), zero_mul]
      · have : k < (l : ℕ) := by
          rcases Nat.lt_or_ge k l with h | h
          · exact h
          · exact absurd (Fin.ext (by simp; omega)) hl
        rw [Krylov.hessenberg_pow_apply_eq_zero T hT k l 0 (by simp; omega), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 2.5]: `e_mᵀ T_m^{m-1} e₁ = ∏_{j=1}^{m-1} (T_m)_{j+1,j}`, at `T_m` of size `m + 1`
here. -/
theorem Krylov.hessenberg_pow_apply_last_eq_prod (T : Mat R (m + 1) (m + 1))
    (hT : ∀ i k : Fin (m + 1), (k : ℕ) + 1 < i → T i k = 0) :
    (T ^ m) (Fin.last m) 0 = ∏ j : Fin m, T j.succ j.castSucc :=
  Krylov.aux_hessenberg_pow_apply_eq_prod T hT m le_rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
