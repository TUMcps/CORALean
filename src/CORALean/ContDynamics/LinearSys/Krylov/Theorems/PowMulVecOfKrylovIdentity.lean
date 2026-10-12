import CORALean.ContDynamics.LinearSys.Krylov.Theorems.HessenbergPowApplyEqZero

/-!
# The Krylov identity is exact below the Krylov order

[1, Eq. 2.4]: from the Krylov identity (2.2), `A V_m = V_m T_m + τ_{m+1,m} v_{m+1} e_mᵀ`, and the
upper Hessenberg structure of `T_m`, `Aʲ v = V_m T_mʲ e₁` for `0 ≤ j ≤ m - 1`, `v = V_m e₁`. By
induction on `j`: `A V_m x = V_m T_m x + τ_{m+1,m} x_m v_{m+1}`, and `x = T_mʲ e₁` has `x_m = 0`
for `j ≤ m - 2` (`hessenberg_pow_apply_eq_zero`, (2.3)). Over any commutative ring, so for
the complex `A` and `T_m` of [1]; no orthogonality of `V_m` is needed.

## References

* [1] T. Jawecki, W. Auzinger, O. Koch. "Computable upper error bounds for Krylov approximations
  to matrix exponentials and associated φ-functions". BIT Numerical Mathematics, 60(1):157-197,
  2020.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {R : Type*} [CommRing R] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 2.4]: `Aʲ (V_m e₁) = V_m T_mʲ e₁` for `j ≤ m - 1`, from (2.2) with `T_m` upper
Hessenberg, at `V_m` with `m + 1` columns here, so for `j ≤ m`. -/
theorem Krylov.pow_mulVec_of_krylovIdentity (A : Mat R n n) (V : Mat R n (m + 1))
    (T : Mat R (m + 1) (m + 1)) (τ : R) (w : Fin n → R)
    (hT : ∀ i k : Fin (m + 1), (k : ℕ) + 1 < i → T i k = 0)
    (hK : A * V = V * T + τ • vecMulVec w (Pi.single (Fin.last m) 1)) {j : ℕ} (hj : j ≤ m) :
    A ^ j *ᵥ (V *ᵥ Pi.single 0 1) = V *ᵥ (T ^ j *ᵥ Pi.single 0 1) := by -- --- PROOF ---
  induction j with
  | zero => rw [pow_zero, pow_zero, one_mulVec, one_mulVec]
  | succ j ih =>
    have hlast : (T ^ j *ᵥ Pi.single 0 1) (Fin.last m) = 0 := by
      rw [mulVec_single_one]
      exact Krylov.hessenberg_pow_apply_eq_zero T hT j _ _ (by simp; omega)
    rw [pow_succ', ← mulVec_mulVec, ih (by omega), mulVec_mulVec, hK, add_mulVec, smul_mulVec,
      vecMulVec_mulVec, single_one_dotProduct, hlast, MulOpposite.op_zero, zero_smul, smul_zero,
      add_zero, mulVec_mulVec, Matrix.mul_assoc, ← pow_succ', ← mulVec_mulVec]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
