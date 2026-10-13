module

public import CORALean.Global.Tensor
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# The defect of the Krylov approximation is a multiple of the next Krylov vector

[1, Eq. 2.9]: with the Krylov identity (2.2), `A V_m = V_m T_m + τ_{m+1,m} v_{m+1} e_mᵀ`, the
defect `D_m(s)v = σ A V_m e^{σsT_m}e₁ - σ V_m T_m e^{σsT_m}e₁` is
`σ(A V_m - V_m T_m)e^{σsT_m}e₁ = σ τ_{m+1,m} (e_mᵀ e^{σsT_m}e₁) v_{m+1}`. The step is linear
algebra and holds for every vector `y` in place of `e^{σsT_m}e₁`; over any commutative ring, so
for the complex `A`, `T_m`, `σ` of [1]. The integral of its norm is the error bound (3.1b) that
[1, Thm. 1] estimates.

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

variable {R : Type*} [CommRing R] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 2.9]: `σ A V_m y - σ V_m T_m y = σ τ_{m+1,m} (e_mᵀ y) v_{m+1}` under (2.2), here for
`V_m` with `m + 1` columns; [1] takes `y = e^{σsT_m}e₁`. -/
theorem Krylov.defect_of_krylovIdentity (A : Mat R n n) (V : Mat R n (m + 1))
    (T : Mat R (m + 1) (m + 1)) (τ σ : R) (w : Fin n → R)
    (hK : A * V = V * T + τ • vecMulVec w (Pi.single (Fin.last m) 1)) (y : Fin (m + 1) → R) :
    σ • (A *ᵥ (V *ᵥ y)) - σ • (V *ᵥ (T *ᵥ y)) = (σ * τ * y (Fin.last m)) • w := by
  rw [mulVec_mulVec, hK, add_mulVec, smul_mulVec, vecMulVec_mulVec, single_one_dotProduct,
    ← mulVec_mulVec, smul_add, add_sub_cancel_left, op_smul_eq_smul, smul_smul, smul_smul]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
