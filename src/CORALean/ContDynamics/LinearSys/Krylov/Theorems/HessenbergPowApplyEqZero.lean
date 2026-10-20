module

public import CORALean.Global.Tensor
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# Powers of a Hessenberg matrix below their subdiagonal band

[1, Eq. 2.3]: for the upper Hessenberg `T_m` of the Krylov identity (2.2),
`e_mᵀ T_mʲ e₁ = 0` for `j = 0, …, m - 2`. Each factor of an upper Hessenberg matrix moves an
entry at most one row down, so `(Tʲ)_{i,l} = 0` when `i > l + j`; the printed case is row `m`,
column `1`. Over any semiring, so for the complex `T_m` of [1].

## Inputs
* `T` – Hessenberg matrix

## Hypotheses
* `hT` – matrix is upper Hessenberg

## Conclusion
* entries of its powers below the band vanish

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

variable {R : Type*} [Semiring R] {m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 2.3]: `(Tʲ)_{i,l} = 0` for an upper Hessenberg `T` when `i > l + j`; at row `m`,
column `1` this is `e_mᵀ T_mʲ e₁ = 0` for `j ≤ m - 2`. -/
theorem Krylov.hessenberg_pow_apply_eq_zero (T : Mat R m m)
    (hT : ∀ i k : Fin m, (k : ℕ) + 1 < i → T i k = 0) :
    ∀ (j : ℕ) (i l : Fin m), (l : ℕ) + j < i → (T ^ j) i l = 0 := by -- --- PROOF ---
  intro j
  induction j with
  | zero =>
    intro i l h
    rw [pow_zero, Matrix.one_apply_ne]
    intro hil
    rw [hil] at h
    omega
  | succ j ih =>
    intro i l h
    -- `(T^{j+1})_{i,l} = Σ_k T_{i,k}(Tʲ)_{k,l}`, and every term has a zero factor
    rw [pow_succ', Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : (k : ℕ) + 1 < i
    · rw [hT i k hk, zero_mul]
    · rw [ih k l (by omega), mul_zero]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
