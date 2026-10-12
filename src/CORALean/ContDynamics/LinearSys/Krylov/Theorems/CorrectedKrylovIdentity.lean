import CORALean.Global.Tensor
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin

/-!
# The corrected Krylov approximation is a Krylov approximation of one dimension more

[1, Thm. 3]'s setting: with `T⁺_m = [T_m 0; τ_{m+1,m}e_m* 0]` (5.2a) and `V⁺_m = [V_m v_{m+1}]`
(5.3), the Krylov identity (2.2) gives `AV⁺_m = V⁺_mT⁺_m + (Av_{m+1})e_{m+1}*`, a Krylov identity
of dimension `m + 1` with `τ = 1` and next vector `Av_{m+1}`; `T⁺_m` is upper Hessenberg with
subdiagonal product `γ_mτ_{m+1,m}`, and `V⁺_me₁ = V_me₁`. So the corrected approximation (5.4)
is the standard one for this identity, and (2.4)-(2.12) apply to it.

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

/-- [1, Thm. 3]'s step: `AV⁺_m = V⁺_mT⁺_m + (Av_{m+1})e_{m+1}*`, `T⁺_m` upper Hessenberg with
subdiagonal product `γ_mτ_{m+1,m}`, and `V⁺_me₁ = V_me₁`; `V_m` has `m + 1` columns. -/
theorem Krylov.correctedKrylov_identity (A : Mat R n n) (V : Mat R n (m + 1))
    (T : Mat R (m + 1) (m + 1)) (τ : R) (w : Fin n → R)
    (hH : ∀ i k : Fin (m + 1), (k : ℕ) + 1 < i → T i k = 0)
    (hK : A * V = V * T + τ • vecMulVec w (Pi.single (Fin.last m) 1)) :
    let Tp : Mat R (m + 2) (m + 2) := Matrix.of fun i j =>
      Fin.lastCases (Fin.lastCases 0 (fun j' => if j' = Fin.last m then τ else 0) j)
        (fun i' => Fin.lastCases 0 (fun j' => T i' j') j) i
    let Vp : Mat R n (m + 2) := Matrix.of fun i j => Fin.lastCases (w i) (fun j' => V i j') j
    A * Vp = Vp * Tp + (1 : R) • vecMulVec (A *ᵥ w) (Pi.single (Fin.last (m + 1)) 1) ∧
      (∀ i k : Fin (m + 2), (k : ℕ) + 1 < i → Tp i k = 0) ∧
      ∏ j : Fin (m + 1), Tp j.succ j.castSucc = (∏ j : Fin m, T j.succ j.castSucc) * τ ∧
      Vp *ᵥ Pi.single 0 1 = V *ᵥ Pi.single 0 1 := by -- --- PROOF ---
  intro Tp Vp
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- column by column: the last is `Av_{m+1}`, the others (2.2)
    ext i j
    have hKij := congrFun (congrFun hK i)
    refine Fin.lastCases ?_ (fun j' => ?_) j
    · simp [Tp, Vp, Matrix.mul_apply, Fin.sum_univ_castSucc, vecMulVec_apply, mulVec,
        dotProduct]
    · have h := hKij j'
      simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply,
        smul_eq_mul] at h
      simp only [Tp, Vp, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_castSucc,
        Fin.lastCases_castSucc, Fin.lastCases_last, Matrix.add_apply, Matrix.smul_apply,
        vecMulVec_apply, smul_eq_mul]
      rw [h]
      by_cases hj : j' = Fin.last m <;> simp [hj, mul_comm, Fin.sum_univ_castSucc]
  · -- `T⁺_m` keeps `T_m`'s Hessenberg structure
    intro i k hik
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl <;>
      rcases Fin.eq_castSucc_or_eq_last k with ⟨k', rfl⟩ | rfl
    · simpa [Tp] using hH i' k' (by simpa using hik)
    · simp at hik; omega
    · have hk : k' ≠ Fin.last m := fun h => by subst h; simp at hik
      simp [Tp, hk]
    · simp [Tp]
  · -- the subdiagonal of `T_m`, then `τ_{m+1,m}`
    rw [Fin.prod_univ_castSucc]
    congr 1
    · refine Finset.prod_congr rfl fun j _ => ?_
      simp only [Tp, Matrix.of_apply, Fin.lastCases_castSucc]
      rw [Fin.succ_castSucc, Fin.lastCases_castSucc]
    · rw [Fin.succ_last]
      simp [Tp]
  · ext i
    simp only [Vp, Matrix.mulVec_single_one, Matrix.col_apply, Matrix.of_apply]
    rw [← Fin.castSucc_zero, Fin.lastCases_castSucc]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
